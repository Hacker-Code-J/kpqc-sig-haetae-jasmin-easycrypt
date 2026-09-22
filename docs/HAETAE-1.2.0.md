# HAETAE-1.2.0 작업 기준

## 출처와 범위

2026-09-17 재정비 시 작업 디렉터리에 있던 `HAETAE-1.2.0/`을 그대로 기준선으로
채택했다. `reference_implementation/CMakeLists.txt`의 프로젝트 버전은 `1.2.0`이다.
참조 구현, 테스트/벤치마크 소스, KAT, MIT 라이선스를 포함하며 최적화 구현은 없다.

[공식 HAETAE 배포 안내](https://kpqc.cryptolab.co.kr/haetae)는 구현 1.2.0의
hyperball sampler 변경과 대응 명세 260825 및 260904를 명시한다.

- [공식 1.2.0 배포 파일](https://drive.google.com/file/d/1pW6YS1wZ1gm8Neb8pY5EyYTkkdRIDmJ6/view)
- 공식 배포 ZIP의 공지 SHA-256:
  `e54f8f962eefadbb2929bca292797bc7ca18769fb9a273c10204f3887fd83e84`
- [대응 명세 260904](https://drive.google.com/file/d/1H2SFqZFG5BcWH--bJKssvXaSG0Sd3mUx/view)
- [UPSTREAM-SHA256SUMS](UPSTREAM-SHA256SUMS): 이 저장소에 제공된 파일 67개의
  SHA-256. ZIP 자체의 해시와는 별개의 파일별 무결성 기록이다.

공식 링크에서 ZIP을 내려받아 공지 해시와 일치함을 확인했고, 제공된 파일
67개 모두가 그 ZIP의 동일 경로 파일과 바이트 단위로 일치했다.
배포 ZIP과 macOS 메타데이터는 소스 트리에 중복 보관하지 않는다.

## 먼저 다시 확인할 부분

기존 `haetae-ref`와 새 참조 소스를 비교했을 때 다음 변화가 확인된다.
이전 경로는 [보관 태그](../archive/README.md)에서 열 수 있다.

| 항목 | 기존 구현 | 1.2.0의 기준 소스 |
| --- | --- | --- |
| Gaussian CDT | 16비트, 64항목 | `src/sampler.c`: 83비트, 166항목의 `sample_gauss83` |
| 한 번의 샘플링 입력 | 17바이트 | `src/sampler.c`: `GAUSS_RAND_BYTES = 26` |
| 지수함수 근사 | 이전 다항식 | `src/sampler.c`: 10차 `approx_exp`와 새 정수 계수 |
| 곱셈 반올림 | 이전 규칙 | `include/fixpoint.h`: `smulh48`의 올림 |
| 샘플 값 반올림 | 이전 결합 시프트 | `src/sampler.c`: 상·하위 limb를 나눈 계산 |

위 파일 경로는 모두 `HAETAE-1.2.0/reference_implementation/` 아래에 있다.
기존 Jasmin 샘플러의 17바이트 입력·stride·버퍼 크기와 이에 의존하는 증명은
새 구현으로 옮긴 뒤 다시 검증해야 한다. `params.h`의 바이트가 기존 참조본과
같다는 사실만으로 샘플러 분포나 전체 알고리즘의 동등성을 주장할 수 없다.
`mode2`/HAETAE-2는 파라미터 집합 이름이며 배포 버전 1.2.0과 구분한다.

## 구현 상태와 후속 순서

[haetae-1.2.0-jasmin](../haetae-1.2.0-jasmin/README.md)에 새 구현을 두었다.
위 샘플러 변경과 난수 소비·refill 규칙을 이식했고, 8개 공개/내부 API와
mode 2·3·5 공식 KAT, 실제 C 소스와의 차등·상호운용 테스트를 연결했다.
[검증 기록](haetae-1.2.0-jasmin-validation.md)에 재현 명령과 한계를 정리한다.

새 [EasyCrypt 프로젝트](../haetae-1.2.0-easycrypt/README.md)에서는 CDT·올림 곱셈·
Horner 계산·단일 Gaussian 시도·유한 소비기의 승인 순서와 제곱합·실제 서명
offset 소비기·SHAKE 초기화와 스트림·실제 서명용 전체 Gaussian 함수·NTT·
API 보조함수의 정리를 검증했다. 이어서 실제 Hyperball 전체 함수와 mode 2·3·5를
word 명세에 연결했다. 기본 전체 정리는 종료한 실행에 적용한다. Gaussian에는
구체적 입력 스트림의 충분한 유한 접두 구간 전제 아래 종료 정리를 추가했다.
검증 범위와 남은 전제는 [CLAIMS.md](../haetae-1.2.0-easycrypt/CLAIMS.md)에 있다.
전체 구현 정확성은 다음 순서로 이어간다.

1. 아래 기준선 검증을 유지하면서 명세 260904와 함수별 대응표를 작성한다.
   CDT에는 명세 §5.1.1과 참고문헌 [21]의 Gaussian 정의를 연결했다. 독립적인
   무한 분포 정의와 실제 Jasmin의 균등 83비트 입력 실험 사이의 통계적 거리가
   2^-78보다 작다는 정리를 추가했다. 출처·수치 인증서·정확한 난수 범위는
   [CDT 명세 대응](../haetae-1.2.0-easycrypt/docs/cdt-distribution-correspondence.md)에 있다.
   Listing 1의 지수함수 근사에는 실제 입력 범위와 signed Horner 의미를 연결하여
   정규화 출력 오차≤27/2^48<2^-43을 증명했다. 실제 양자화 지수·rounded-zero를
   유지한 조건부 승인 확률도 다룬다. [수치 증명 경계](../haetae-1.2.0-easycrypt/docs/approx-exp-mathematical-bound.md)를 참조한다.
   실제 xi와 반올림 전 Gaussian 지수 사이의 오차≤2^-49, 두 zero 규칙의
   예외 구간도 연결했다. 명시적인 균등 72+48비트 단일 시도에서 평균 승인 확률
   차이<29/2^48<2^-43을 증명한다. [반올림 전 수락식 연결](../haetae-1.2.0-easycrypt/docs/raw-gaussian-acceptance.md)을 참조한다.
   이어서 실제 균등 83+72+48비트 실험과 무한 Gaussian CDT 목표 사이에서,
   모든 출력 집합의 승인·출력 공동 확률 차이<29/2^48+2^-78을 증명한다.
   [공동 출력 확률](../haetae-1.2.0-easycrypt/docs/joint-accepted-output.md)은 승인 후 정규화 전의 정리다.
   실제·이상적 승인 확률의 하한 1/7·1/8을 증명하고, 승인 후 조건부분포를
   비교해 통계적 거리<2^-39까지 연결했다. [조건부분포 범위](../haetae-1.2.0-easycrypt/docs/conditional-accepted-output.md)는
   이전 이상적 실험을 정규화한 목표다. 후속 [Gaussian 질량식 식별](../haetae-1.2.0-easycrypt/docs/gaussian-magnitude-identification.md)에서
   이를 exp(-k²/2^153)로 정의한 정수 Gaussian의 절댓값 반올림 분포와 정확히
   연결했다. 실제 조건부분포의 거리<2^-39가 이 명시적인 목표에도 그대로 적용된다.
   독립 균등 입력으로 실제 시도를 반복 호출하는 실험의 확률 1 종료와 첫 승인값의
   정확한 조건부분포도 증명했다. 256·257개 승인 목록의 결합분포 및 유한 후보
   스트림과의 연결은 [반복·목록 증명](../haetae-1.2.0-easycrypt/docs/gaussian-retries-and-batches.md)에 있다.
   [전체 iid 버퍼 모형](../haetae-1.2.0-easycrypt/docs/gaussian-iid-buffer.md)은
   균등 바이트 공급과 실제 소비·carry 함수를 합성해, 충분한 접두 구간 전제 없이
   확률 1 종료와 저장되는 256개 크기의 정확한 결합분포·Gaussian 거리<2^-31을 증명한다.
   후속 [부호 출력 단계](../haetae-1.2.0-easycrypt/docs/gaussian-signed-output.md)는
   명시적 iid 바이트 모형에서 256개 공정 부호와 전체 표본 배열·제곱 워드 상태의
   독립성을 증명한다. 실제 반환값의 `±W64.to_uint` 관측을
   `sign(G)·floor((|G|+32768)/65536)` 목표에 연결해 256개 벡터 거리<2^-31을 얻는다.
   0은 0으로 남고 ±32768은 각각 ±1로 반올림한다. 실제 scaling 뒤 부호 연산도
   word 단위로 정확하며, signed32 해석은 명시적 fit 조건을 유지한다.
   구체적인 SHAKE로의 확률 보장 전달은 별도로 남아 있다.
2. 단일 Gaussian 시도에서 유한 소비기의 전체 출력·승인 표본열·제곱합 누적
   fold까지 연결했다. 초기 limb 범위를 포함한 정확한 전제는 정리에 명시한다.
3. 실제 `_sf_sample_gauss_N_full_at`의 seed/nonce 초기화, 49블록, 부호 바이트와
   반복 refill을 연속 word 스트림 명세에 연결했다. 여러 Gaussian 호출의
   초기 제곱합 조건, Hyperball 고정소수점·scaling·모듈러 norm·retry도 합성했다.
   정수 반경 보장과 word 승인은 구분한다. 구성한 후보열의 wrap 사례와 전제는
   [수치 경계 기록](../haetae-1.2.0-easycrypt/docs/hyperball-numerical-boundary.md)에 있다.
   부호 단계의 scaling 연결은 정확한 word 부호 계산과, 반올림 크기가
   2147483647 이하일 때의 signed32 해석을 다룬다. 국소 Gaussian 창을 전역
   scaling 인덱스에 연결할 때는 `sample_offset=8*sign_offset`를 명시한다.
   Hyperball 전체의 실수 근사 오차·분포·종료성은 별도 의무다.
   [실제 helper 반례 증명](../haetae-1.2.0-easycrypt/docs/hyperball-actual-witnesses.md)은
   지정 후보열에서 실제 소비·두 더미 제곱 누적·Newton6·scaling·norm을 합성했다.
   세 모드 모두 정수 반경 초과에도 승인1을 반환하는 결과를 증명한다.
   SHAKE seed나 전체 seeded Hyperball 경로의 도달성, 예외 사건 확률은 별도다.
   [입력 안전 구간](../haetae-1.2.0-easycrypt/docs/hyperball-safe-domain.md)은 canonical
   제곱합 S∈[3D/4,5D/4]·2^76에서 실제 Newton·scaling 계수≤2^26과 정수 노름의
   무오버플로를 도출한다. 임의 표본·부호에 대한 승인⇒반경 보장이며, 구간 발생
   확률과 실제 seed·외부 retry·이상적 분포는 별도로 남아 있다.
4. NTT·코덱 등 재사용 후보를 태그에서 필요한 만큼 가져와 현재 소스와 비교한다.
   이후 KeyGen/Sign/Verify 합성, 종료성·분포·보안 의무를 구분하여 진행한다.

과거 검증 로그를 새 Jasmin 소스의 증명 결과로 사용하지 않는다. 재사용한 NTT
지원 이론도 새 디렉터리에서 각각 주 검증 대상으로 다시 검사했다.

<!-- gaussian-payload:milestone:start -->
후속 [전체 승인 payload·제곱합 단계](../haetae-1.2.0-easycrypt/docs/gaussian-payload-and-squares.md)는
명시적 iid 바이트와 초기 제곱합 0에서 모드 2·3·5의 Gaussian 배치 전체를 연결한다.
요청 `257, 257, 256, ...`, 표본 offset `256*i`, 부호 offset `32*i`를 따라
실제 sign-copy·carry·유한 소비기를 호출한다. `hip_initial`의 표본·부호 0 초기화는
증명 모형의 선택이다. 생산 코드가 초기화하는 배열은 제곱합이며, 전체 생산 상태나
seeded 실행과의 동치를 주장하지 않는다.

D=1538·2306·2818개의 승인 payload 이력에서 0부터 센 위치 256·513은 가시
벡터에서만 빠지고, 모든 raw 제곱은 S에 남는다. 이 동일한 이력의 사영으로
가시 벡터·S의 결합분포와 안전 구간 사건의 정확한 확률식을 증명했다. 그 단계에서는
구간 이탈의 수치 상한, raw 제곱의 이상적 Gaussian·chi-square 법칙, SHAKE·외부 Hyperball
retry·전체 API 연결을 후속 의무로 남겼다. 생산 변경이 없어 해당 단계에서 KAT를 재실행하지 않았다.
<!-- gaussian-payload:milestone:end -->

<!-- hyperball-tail:milestone:start -->
후속 [iid 제곱합 꼬리·단일 시도 경계](../haetae-1.2.0-easycrypt/docs/hyperball-iid-tail-bound.md)는
D=1538·2306·2818개의 실제 승인 payload에 대해 안전 구간 이탈 확률을 각각
2^-29·2^-44·2^-54 미만으로 증명한다. q=floor(Z²/2^76)의 지수 모멘트와
검사된 실수 지수 계수·정수 거듭제곱 인증서를 사용한다. q는 rounded 표본의 제곱이 아니다.
실제 Gaussian 배치와 실제 Newton·scaling·norm 호출을 합성한 한 번의 iid 시도에서,
승인과 정수 제곱 노름 초과의 결합 사건에도 같은 상계를 얻는다.

초기 제곱합은 0이며, 표본·부호까지 0으로 두는 기존 `hip_initial`은 증명 모형의
선택이다. 생산 코드는 제곱합만 초기화한다. 이 결과는 승인 조건부 확률,
외부 retry 전체나 구체적 SHAKE/seeded Hyperball의 확률 보장을 뜻하지 않는다.
기존 단계 기록의 수치 꼬리 경계 의무를 iid 모형에서 해소한 후속 결과이며,
생산 변경 없이 추가한 증명이므로 이번 단계에서 KAT를 재실행하지 않았다.
<!-- hyperball-tail:milestone:end -->

## 재현과 검증 한계

```sh
# 저장소 루트에서
bash scripts/check-baseline.sh
```

2026-09-17 정리 전 기준선에서 `ref` mode 2·3·5 KAT의 `.req`·`.rsp` 6개가
모두 일치했고, 배포본의 `kat/SHA256SUMS` 검사도 통과했다. KAT를 생성해
덮어쓰는 `kat.sh update`는 이 검증에 사용하지 않는다.

KAT 일치는 제공된 C 구현의 재현성 검사다. 샘플러 분포의 정확성이나
Jasmin/EasyCrypt 검증을 대신하지 않는다. 특히 `test/test_sampler.c`는 기본
CMake 테스트 대상에 포함되지 않고 자체 근사함수를 포함하므로 production
샘플러의 검증 근거로 계산하지 않는다. `test/main.c`도 실패를 출력한 뒤 0으로
종료할 수 있어 실행 종료 코드만으로 성공을 판단하지 않는다.

정리 시점의 과거 증명 결과와 미해결 항목은 `archive`에 보존한다. 과거 전체
EasyCrypt 검증은 이번 구조 변경에서 다시 실행하지 않았다.
