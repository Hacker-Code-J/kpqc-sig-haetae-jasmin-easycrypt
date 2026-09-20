# HAETAE-1.2.0 Jasmin / EasyCrypt

[현재 Jasmin 구현](../haetae-1.2.0-jasmin/README.md)에서 직접 추출한 프로그램에 대해
구성요소의 기능 정확성을 증명하는 작업 공간이다. KAT 실행 결과와 구분하여
EasyCrypt가 실제로 검사한 명세·정리·의존 이론을 보관한다.

현재 증명 범위는 **CDT, 고정소수점 곱셈·다항식, 단일 Gaussian 시도, 유한
소비기의 정확한 출력·승인 순서·제곱합, 서명용 전체 Gaussian 스트림 함수,
고정 길이 SHAKE 초기화·반복 블록, 서명용 Hyperball 전체 함수와 mode 2·3·5,
NTT, 실제 API 메모리 보조함수**다. 전체 Gaussian·Hyperball 정리는 종료한 실행의
word 결과에 대한 Hoare 정리다. 전체 KeyGen/Sign/Verify와
Sign→Verify 합성의 정확성 증명은 아직 완료하지 않았다.

83비트 CDT에는 별도의 수학적 분포 정리가 있다. **균등 83비트 입력에서 실제
Jasmin CDT의 출력 분포와 비음수 이산 Gaussian(σ=16)의 통계적 거리는
2^-78보다 작다.** 목표 분포는 공식 명세와 참고문헌의 수식에서 정의했으며,
그 무한 정규화·꼬리 상한·수치 인증서도 검증한다.
[명세 대응과 범위](docs/cdt-distribution-correspondence.md)를 참조한다.

## 검증된 핵심 결과

| 대상 | 결과 |
| --- | --- |
| 83비트 CDT | 실제 임계값 개수와 일치, 반환 범위 0…166, 최대 입력에서 166, 종료성 |
| CDT의 수학적 분포 | 균등 83비트 입력 실험의 정확한 확률 질량; 공식 비음수 Gaussian(σ=16)과 통계적 거리 <2^-78, 모든 출력 집합의 확률 차이 상한 |
| `smulh48` | 모든 입력에서 `ceil(signed(a) × unsigned(b) / 2^48)`의 64비트 표현과 일치 |
| `approx_exp` | C에서 독립 추출한 10차 Horner 계산과 일치; 각 곱셈의 정수 올림 의미 연결 |
| 단일 Gaussian 시도 | 모든 26바이트 입력의 표본·제곱 limbs·승인 비트가 명세와 일치하고 종료 |
| 표본 반올림 | 실제 결과와 정수식의 일치 및 `0…12033618204333965312 < 2^64`; CDT 166 포함 |
| 유한 Gaussian 소비기 | 26바이트 후보열을 처리한 전체 반환값과 명세 fold의 일치; 승인 개수·저장된 승인 순서·dummy 슬롯 보존·종료성 |
| 제곱합 | 초기 두 limb가 각각 48비트 범위이고 요청이 512개 이하일 때 승인 후보의 제곱 limbs에 대한 정확한 정수 합; 실제 square-high `<2^38` |
| 서명 offset 소비기 | 실제 `__sample_gauss_at`에 출력·순서·정수 제곱합을 연결하고 요청 영역 밖을 보존 |
| refill 경계 | 실제 carry의 잔여 바이트 보존·종료, carry와 새 136바이트 블록의 결합 배치 |
| SHAKE 단일 블록 | 실제 서명 코드의 24라운드 word 순열, 반환 상태의 136바이트 직렬화, 출력 범위 밖 보존·종료 |
| SHAKE seed 초기화 | seed 64바이트·nonce 하위 16비트·domain/padding의 전체 200바이트 상태 일치·종료 |
| 서명용 전체 Gaussian 함수 | 실제 `_sf_sample_gauss_N_full_at`의 초기 49블록·32바이트 부호·반복 refill을 연속 스트림 명세에 합성; `n=256/257`에서 종료 시 표본·부호·정수 제곱합·외부 영역 보존 |
| Hyperball 누적합 | 최대 2,818개 승인 후보에서 두 limb의 48비트 범위를 증명하여 연속 Gaussian 호출 연결 |
| 고정소수점·scaling | 실제 word 곱셈·정규화·반분·Newton 6회 갱신·부호 및 signed32 출력·보존·종료; 수치 fit는 명시적 조건 |
| 서명용 전체 Hyperball | 실제 전체 함수·mode 2/3/5를 배치 스트림·최초 승인 이력·모듈러 norm·최종 바이트와 카운터에 연결; 반환값 유일성 |
| NTT·역 NTT | 명시적 계수 범위 아래 256점 수학적 변환과 결과 범위·종료성 |
| 실제 API 보조함수 | 서명 문맥 prefix, 안전한 겹침의 역방향 복사, 검증 실패 시 영 초기화와 외부 메모리 보존 |

샘플러 주요 정리는 별도로 추출한 실제 서명 프로그램의 내부 함수에도 연결한다.
정확한 정리 이름·전제와 미완료 항목은 [CLAIMS.md](CLAIMS.md), 검증 결과는
[VALIDATION.md](VALIDATION.md)에 있다.

## 재현

현재 사용한 Jasmin / `jasmin2ec`는 2026.03.0이다. EasyCrypt, Jasmin의 EasyCrypt
라이브러리, Why3 및 설정된 SMT 증명기가 필요하다. 바이너리 해시와 추출 설정은
[toolchain.json](manifests/toolchain.json)에 기록했다.

```sh
make -C haetae-1.2.0-easycrypt verify
```

이 명령은 다음 순서로 진행한다.

1. 고정된 공식 배포본·Jasmin 입력·추출물·NTT 지원 이론의 해시 확인.
2. 현재 Jasmin에서 재추출하여 생성 파일 전체를 비교하고, C 상수와 수학적 구간 인증서를 다시 생성해 비교.
3. 증명 생략 pragma, 새 가정 선언, 미완성 증명, 디버그 명령 검사.
4. 생성물과 프로젝트의 **각 이론을 주 검증 대상으로** `-no-eco`, `Proofs:check` 실행.

각 검증에는 마지막 확인 정리를 덧붙인 동일 이름의 임시 복사본을 사용한다.
EasyCrypt가 열린 증명 상태의 EOF에서 성공 코드를 반환하는 경우도 이 확인
정리에서 실패하도록 한다. 원본 파일과 추출물은 변경하지 않는다.

EasyCrypt는 import만 한 파일의 증명 본문을 기본적으로 재검사하지 않는다.
따라서 이 게이트는 마지막 정리 파일 하나의 성공으로 의존 이론 검증을 대신하지
않는다. NTT의 지원 이론까지 새로 검증하므로 전체 실행에는 시간이 걸린다.

필요한 그룹만 확인할 수도 있다. 각 그룹의 PASS는 선택한 그룹에 한정된다.

```sh
make -C haetae-1.2.0-easycrypt verify-new        # NTT 외 로컬 명세와 증명 65개
make -C haetae-1.2.0-easycrypt verify-ntt        # NTT 지원 이론 11개 + 현재 구현 정리
make -C haetae-1.2.0-easycrypt verify-generated  # 추출물 102개 로딩/타입 검사
make -C haetae-1.2.0-easycrypt test-gate         # 미완성 증명·수치 인증서·비교 표 변조 거부
make -C haetae-1.2.0-easycrypt test-hyperball-boundary  # 구성한 후보열의 C/Jasmin 수치 경계 재현
```

로그와 실행별 SHA-256·종료 코드는 `logs/`에 기록한다. `latest-<group>.json`은
실행 시작 시 RUNNING으로 바뀌고, 사전 검사 실패도 FAIL로 남는다. `.eco`와 로그는
Git에서 제외한다. 샌드박스가 Why3의 로컬 Unix 소켓 실행을 막는 경우에는 검증기
실행 권한이 필요하며, 이 오류를 증명 성공으로 처리하지 않는다.

## 파일 구성과 신뢰 경계

- `generated/`: 원본 Jasmin에서 자동 추출한 프로그램과 배열 이론. 직접 수정하지 않는다.
- `theories/`: 명세와 필요한 NTT 수학 이론. C의 CDT·계수는 독립 생성기로 가져온다.
- `proofs/`: 실제 추출 프로시저의 Hoare/pHoare 정리와 수학적 분포·오차 정리.
- `scripts/`: 재추출, 상수 생성, 무결성 검사와 검증 게이트.
- `manifests/`: 입력·추출물·검증 대상·이전 NTT 이론의 출처와 해시.

검증은 Linux x86-64, `barray`, Jasmin의 `normal` 의미 모델에 대한 것이다.
EasyCrypt/SMT, Jasmin 추출기와 모델 라이브러리는 신뢰하는 도구에 포함된다.
NTT 지원에는 기록된 산술 가정이 남아 있으므로 전체 프로젝트를 공리 없는
검증이라고 부르지 않는다. 구체적인 내용은
[NTT 가정 목록](manifests/ntt-assumptions.md)을 참조한다.

메모리 정리는 총 byte map과 추출된 배열 객체에 대한 계약이다. 운영체제의 실제
메모리 할당·접근 가능성, C descriptor 래퍼나 생성된 어셈블리 자체에 대한 별도의
검증을 의미하지 않는다. SHAKE 정리는 고정 길이 seed·nonce의 흡수·패딩과
word 순열 스트림을 다루며, FIPS bit 명세와의 별도 동치나 임의 길이 입력의
sponge 정리는 포함하지 않는다. CDT 분포 정리의 균등 입력은 확률 실험에 명시되어
있으며 실제 SHAKE의 성질로 가정하지 않는다. sigma76 지수 근사·거부와의 분포
합성, 전체 거부 루프의 종료·분포, 전체 서명 정확성·보안은 남아 있다.

Hyperball의 승인 norm은 64비트 모듈러 합이다. 수학적 제곱합의 반경 보장은
오버플로 조건을 추가로 충족해야 한다. 구성한 후보열에서 C와 Jasmin의 동일한
wrap 동작을 재현했으며, 실제 SHAKE 시드 도달 가능성을 주장하지 않는다.
정확한 사례와 검증 명령은 [수치 경계 기록](docs/hyperball-numerical-boundary.md)에 있다.
