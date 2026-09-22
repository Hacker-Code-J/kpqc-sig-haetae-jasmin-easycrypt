# HAETAE-1.2.0 — Jasmin / EasyCrypt

HAETAE-1.2.0의 C 참조 구현과 이에 대응하는 Jasmin 구현을 관리하는 저장소다.
Jasmin의 mode 2·3·5 KAT, 샘플러 차등 테스트와 C 상호운용 테스트를 포함한다.
별도 EasyCrypt 프로젝트에서 새 샘플러의 승인 순서·제곱합과 실제 서명용
Gaussian 함수의 전체 SHAKE/refill 흐름, Hyperball 전체 흐름과 mode 2·3·5,
NTT·API 보조함수를 검증한다. Gaussian·Hyperball의 기본 전체 정리는 종료한 실행의
word 반환값에 관한 것이다. Gaussian에는 충분한 승인 후보를 담은 유한 입력 구간이
있을 때의 종료 정리를 추가했다. Hyperball norm의 정수 해석에는 오버플로가 없다는 조건이 필요하다.
전체 KeyGen/Sign/Verify 합성의 형식 검증은 아직 완료하지 않았다.

83비트 CDT에 대해서는 균등 입력을 받은 실제 Jasmin 함수와 공식 목표인 비음수
이산 Gaussian(σ=16)의 **통계적 거리 <2^-78**도 증명한다.
[수학적 명세 대응과 범위](haetae-1.2.0-easycrypt/docs/cdt-distribution-correspondence.md)에
출처·인증서·난수 전제를 기록했다.

실제 지수함수 근사에도 수학적 오차 정리가 있다. 모든 sigma76 입력에서
`approx_exp`의 정규화 출력 오차는 **27/2^48 이하, 2^-43 미만**이다.
[수치·승인 확률 증명의 범위](haetae-1.2.0-easycrypt/docs/approx-exp-mathematical-bound.md)에
실제 입력 범위와 조건부 승인 실험을 설명한다.
실제 지수 입력과 반올림 전 Gaussian 수락식의 관계도 다룬다. 잡음 72비트와
거부 48비트를 명시적으로 균등 생성한 한 번의 시도에서, 평균 승인 확률 차이는
**29/2^48 미만, 따라서 2^-43 미만**이다. 반올림된 0과 실제 0의 차이는 예외
구간의 확률로 포함한다. [수식과 정확한 범위](haetae-1.2.0-easycrypt/docs/raw-gaussian-acceptance.md)를 참조한다.

CDT 입력까지 균등하게 생성한 실제 실험에서는, **모든 출력 집합 S**에 대해
“승인되고 출력이 S에 속할 확률”과 독립적인 이상적 실험의 같은 확률 사이 차이를
**29/2^48+2^-78 미만**으로 증명한다. 이상적 Gaussian의 무한 꼬리와 무제한 정수
반올림을 유지한다. [공동 확률의 정의와 범위](haetae-1.2.0-easycrypt/docs/joint-accepted-output.md)에
승인 후 조건부분포와의 구분을 기록했다.

승인 후 조건부분포도 비교한다. 실제·이상적 승인 확률의 하한 **1/7·1/8**을
증명하고 각자의 승인 확률로 정규화하여, 두 표본 크기 분포의 **통계적 거리
<2^-39**를 증명한다. 비교 대상은 앞선 이상적 실험의 조건부분포다.
[조건부 분포의 정의와 오차](haetae-1.2.0-easycrypt/docs/conditional-accepted-output.md)에
난수 모형과 해당 단계의 증명 범위를 명시한다.

이상적 조건부분포를 **정수 Gaussian G의 절댓값을 2^16으로 나누어 반올림한 분포**와
정확히 식별했다. `Pr[G=k]∝exp(-k²/2^153)`의 무한 정규화와 반올림 구간별
확률도 증명했으므로, 실제 승인 표본 크기와 이 명시적 Gaussian 목표의
**통계적 거리 <2^-39**가 직접 성립한다. [Gaussian 질량식과 증명](haetae-1.2.0-easycrypt/docs/gaussian-magnitude-identification.md)에
0·반올림 경계와 그 단계의 증명 범위를 기록했다.

독립 균등 83·72·48비트 입력으로 실제 Jasmin 시도를 반복 호출하는 실험은
**확률 1로 종료**하며, 첫 승인값은 위 조건부분포와 정확히 같다.
승인된 256개 값의 결합분포는 독립 Gaussian 목표 목록과 **거리 <2^-31**,
257개는 **거리 <257·2^-39**다. 후보 바이트열과 승인 순서, 충분한 유한
접두 구간을 얻을 확률도 연결했다. [반복·표본 목록 증명](haetae-1.2.0-easycrypt/docs/gaussian-retries-and-batches.md)은
이 명시적 난수 모형과 구체적인 SHAKE의 성질을 구분한다.

독립 균등 바이트를 136바이트씩 공급하는 전체 버퍼 모형에도 분포 정리를
연결했다. 이 모형은 실제 Jasmin의 소비·잔여 바이트 복사·부호 복사 함수를
호출하며 **확률 1로 종료**한다. 요청 256/257 모두 실제 저장되는 256개 크기
값의 결합분포가 독립 조건부분포 목록과 정확히 같고, Gaussian 목표와의
**통계적 거리 <2^-31**를 유지한다. [전체 iid 버퍼 증명과 범위](haetae-1.2.0-easycrypt/docs/gaussian-iid-buffer.md)는
균등한 26바이트 입력, 이미 알려진 잔여 바이트, 더미와 word 누적합의 경계를 명시한다.

부호 단계도 증명했다. 명시적 iid 바이트 모형에서 256개 독립 공정 부호는
전체 표본 배열·제곱 워드 상태와 독립이다. 실제 반환값을 `±W64.to_uint(word)`로
관측한 256개 정수의 분포는 `sign(G)·floor((|G|+32768)/65536)` 목표의 독립
목록과 **거리 <2^-31**이다. 실제 scaling 뒤 부호 적용도 word 단위로 정확하며,
signed32 정수 해석은 반올림 크기≤2147483647 조건을 유지한다.
0·반올림 경계, 정확한 입력 조건과 전역 인덱스 정렬은
[부호 출력 증명](haetae-1.2.0-easycrypt/docs/gaussian-signed-output.md)에 기록한다.

Hyperball 수치 경계도 실제 추출 함수에 연결했다. 지정한 후보열을 실제 유한
소비기·Newton·scaling·norm 함수들에 전달한 실행은 mode 2·3·5 모두 종료하고,
**실제 정수 노름이 경계를 넘는데도 word 승인값 1을 반환**한다. 두 더미의 제곱
누적과 signed32 변환의 넘침을 포함한 결과다. 이 실행에 대응하는 SHAKE seed나
전체 서명 API의 도달 가능성을 주장하지 않는다.
[실제 함수 반례 증명](haetae-1.2.0-easycrypt/docs/hyperball-actual-witnesses.md)에
정확한 입력·결과·범위를 기록했다.

Hyperball의 입력 제곱합에 대한 충분한 안전 구간도 증명했다. low limb가 정규형이고
`3D/4 ≤ S/2^76 ≤ 5D/4`이면 실제 Newton·scaling에서 전체 반올림 크기≤2^26,
signed32 변환의 정확성 및 정수 노름의 무오버플로를 얻는다. 여기서 D는 두 더미를
포함한 이벤트 수다. 표본·부호 배열은 제한하지 않으며 **승인되면 실제 반경 이내**임을
증명한다. 이 구간에 들어갈 확률과 전체 seeded 흐름은 별도로 남아 있다.
[입력 안전 구간 증명](haetae-1.2.0-easycrypt/docs/hyperball-safe-domain.md)에 정확한
전제와 실제 호출 계약을 기록했다.

<!-- gaussian-payload:overview:start -->
후속 [전체 승인 payload·제곱합 증명](haetae-1.2.0-easycrypt/docs/gaussian-payload-and-squares.md)은
독립 균등 바이트를 사용하는 Gaussian 배치의 **가시 표본 벡터와 정수 제곱합 S의
정확한 결합분포**를 다룬다. 모드 2·3·5의 전체 승인 이력은 각각
D=1538·2306·2818개다. 같은 이력에서 두 더미는 가시 벡터에서만 제외하고
S에는 포함한다. S는 반올림된 표본의 제곱합이 아니라 실제 raw 제곱 limbs의 합이다.
초기 제곱합 0과 실제 호출 순서·offset에서 안전 구간 사건의 정확한 확률식을 얻었다.
표본·부호 배열도 0으로 두는 것은 증명 모형의 선택이며, 생산 코드는 제곱합만
0으로 초기화한다. 구간 이탈 확률의 수치 상한과 전체 seeded 흐름은 아직 남아 있다.
<!-- gaussian-payload:overview:end -->

| 경로 | 용도 |
| --- | --- |
| [HAETAE-1.2.0/](HAETAE-1.2.0/) | 수정하지 않은 참조 배포본, 라이선스, KAT |
| [haetae-1.2.0-jasmin/](haetae-1.2.0-jasmin/) | 1.2.0 Jasmin 구현, 8개 API, 빌드와 검증 테스트 |
| [haetae-1.2.0-easycrypt/](haetae-1.2.0-easycrypt/README.md) | 실제 Jasmin 추출물의 구성요소 정확성 정리와 검증 게이트 |
| [docs/HAETAE-1.2.0.md](docs/HAETAE-1.2.0.md) | 배포 출처, 버전 차이, 재시작 순서 |
| [scripts/check-baseline.sh](scripts/check-baseline.sh) | 배포본 해시 확인과 참조 KAT 재현 |
| [archive/README.md](archive/README.md) | 과거 핵심 문서, 보관 기준, 전체 이력 복구 방법 |

## 기준선 확인

Linux에서 Bash, CMake 3.18 이상, C11 컴파일러, OpenSSL 개발 파일,
`make`, `diff`, `sha256sum`이 필요하다. 참조 구현이 이미 요구하는 도구들이다.

```sh
bash scripts/check-baseline.sh
```

배포본 SHA-256을 확인한 뒤 mode 2·3·5의 KAT를 생성하여 저장된 `.req`·`.rsp`
6개와 바이트 단위로 비교한다. 생성물은 무시되는
`HAETAE-1.2.0/reference_implementation/build/`에만 생성된다.
이 배포본에는 최적화 구현이 없으므로 검증 대상은 `ref`다.

Jasmin 구현은 Linux x86-64에서 Jasmin Compiler 2026.03.0으로 빌드한다.
자세한 API와 난수 연결 방법은 [구현 안내](haetae-1.2.0-jasmin/README.md),
검증 범위는 [검증 기록](docs/haetae-1.2.0-jasmin-validation.md)에 있다.

```sh
make -C haetae-1.2.0-jasmin -j2 all
make -C haetae-1.2.0-jasmin -j2 test
```

EasyCrypt 구성요소 정리는 다음 명령으로 재검증한다. 정확한 범위와 전제는
[형식 검증 범위](haetae-1.2.0-easycrypt/CLAIMS.md)를 참조한다.

```sh
make -C haetae-1.2.0-easycrypt verify
```

## 작업 방식

- 통합 기준 브랜치는 `main`이다. 작업 브랜치는 짧게 유지하고 검증 후 통합한다.
- `HAETAE-1.2.0/`은 비교 기준으로 보존한다. Jasmin은 별도 디렉터리에서
  개발하고, 검증한 함수와 가정을 함께 기록한다.
- 과거 EasyCrypt 증명은 재사용 후보이며 1.2.0의 검증 결과로 자동 승계하지 않는다.
- 커밋 첫 줄은 `[yymmdd] <유형>: <변경 이유>` 형식을 사용하고
  `Tested:`, `Not-tested:`, `Directive:` 등
  Git-native Lore trailer로 검증 범위와 남은 의무를 기록한다.

과거 브랜치와 미커밋 문서 수정은 `archive/pre-haetae-1.2.0/*` 태그로 보존한다.
기존 Git 이력을 유지하므로 과거의 큰 파일도 이력에는 남아 있다.
