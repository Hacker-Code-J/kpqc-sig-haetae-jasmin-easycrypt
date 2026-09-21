# 검증 기록

2026-09-17~21 작업에서 현재 Jasmin 소스로 재추출하고 EasyCrypt를 실제 실행했다.
기존 버전의 검증 로그나 KAT 결과를 새 증명의 근거로 대체하지 않았다.

| 구분 | 새로 검사한 대상 | 결과 |
| --- | --- | --- |
| 추출물 | 배열 이론과 현재 프로그램 102개 | 앞 단계 모두 PASS; 이번 재추출 일치 확인 |
| NTT 외 명세·증명 | `verify-new`의 128개 파일 | EOF 확인을 포함한 새 통합 실행 모두 PASS |
| NTT | 필요한 지원 이론 11개와 현재 구현 정리 1개 | 앞 단계 각 파일을 주 대상으로 모두 PASS; 이번 해시 불변 확인 |
| 검증기 회귀 | 기존 EOF·상수·Gaussian 인증서 검사 14개와 지수 다항식 인증서 검사 4개 | 18개 모두 PASS |
| CDT 수학적 분포 | 실제 Jasmin의 균등 83비트 입력 분포와 비음수 Gaussian(σ=16) | 모든 출력 집합의 확률 차이 <2^-78 증명 |
| 지수함수 수치 오차 | 모든 sigma76 입력에서 실제 지수 인자 범위와 실제 근사 함수 | 정규화 출력 오차≤27/2^48<2^-43 및 종료 증명 |
| 조건부 승인 확률 | 후보 고정·거부 48비트 균등 입력의 실제 sigma 호출 | 실제 양자화 지수·rounded-zero 기준 확률 차이≤α·28/2^48<2^-43 |
| 반올림 전 지수 | 실제 제곱·지수와 독립적인 Gaussian 밀도 비율 | 모든 26바이트 입력의 지수 오차≤2^-49 |
| 0 보정 차이 | 실제 rounded-zero와 반올림 전 후보 zero | x=0·1≤y<32768에서만 차이; 균등 72비트의 평균 계수 효과<2^-58 |
| 반올림 전 기준 평균 승인 | CDT 바이트 고정·독립 균등 72+48비트의 실제 sigma 호출 | raw Gaussian 수락식의 평균과 확률 차이<29/2^48<2^-43 |
| 모든 출력 집합의 공동 확률 | 실제 균등 83+72+48비트 시도와 무한 Gaussian CDT·무제한 정수 반올림 목표 | 모든 S의 승인·출력 공동 확률 차이<29/2^48+2^-78<30/2^48<2^-43; 정규화 전 |
| 승인 후 조건부분포 | 실제 및 이전 독립 이상적 실험의 native dcond·정수 사영 분포 | 실제 승인≥1/7·이상적≥1/8, 두 조건부분포의 질량 1 및 통계적 거리≤16·(29/2^48+2^-78)<2^-39 |
| 명시적 Gaussian 질량식 | 모든 정수의 exp(-k²/2^153) 독립 정규화와 절댓값 반올림 PMF | 이상적 조건부분포와 정확히 일치; 실제 승인 표본 크기 분포와 통계적 거리<2^-39; 0·구간 경계 포함 |
| Hyperball 수치 재현 | mode 2·3·5의 고정 후보열을 C/Jasmin으로 실행 | 09-18 재현 PASS 보존; 이번 구현 변경·실행 없음 |

전체 로컬 명세·증명 140개를 각 단계에서 주 검증 대상으로 검사했다. import만 된 증명의
본문이 자동으로 재검사된다고 가정하지 않았다. 새 코드 게이트는 `-no-eco`와
명시적 `Proofs:check`를 사용하며, 원래 NTT 지원 재검증도 `-no-eco`의 기본
강한 검사 모드로 개별 실행했다.

이번에는 반복·목록·유한 입력 스트림에 관한 증명 파일 15개를 추가했다.
독립 균등 83·72·48비트로 실제 Jasmin 시도를 반복 호출하는 실험의 확률 1
종료와 정확한 첫 승인값 분포를 증명했다. 전체 승인 목록의 결합분포도
독립 조건부분포 목록과 같으며, 256개 Gaussian 거리<2^-31,
257개 거리<257·2^-39와 앞 256개 사영을 연결했다.

실제 버퍼 함수는 그 seed의 스트림에 충분한 승인 후보를 포함한 유한 구간이
있다는 전제 아래 종료와 정확한 반환값을 증명했다. 그 전제를 모든 seed에 대해
증명한 것은 아니다. 독립 난수의 유한 후보 구간에서 부족 확률이 0으로 수렴하는
결과와 구체적 SHAKE의 확률 성질을 구분한다.

변경 없는 기존 비NTT 113개를 새 증명 작성과 병행하여 먼저 검사하고, 새 15개는
최종 소스 고정 후 검사했다. 모두 같은 `verify-one.sh`의 강한 검사·EOF 확인을
사용했다. 새 파일은 기존 증명의 의존 대상이 아니며, 완료 시 전체 목록과
모든 해시를 다시 대조했다. 실행 명령·시간과 소스 해시는
`manifests/verification-results.json`에 기록했다. 이전 125개 로컬 이론·증명
소스는 변경하지 않았으며, 새 공리나 수치 오라클을 추가하지 않았다.
기존 NTT 12개와 추출물 102개는 이전 새 검증 결과를 보존하고,
해시 불변 및 현재 소스의 재추출 일치를 다시 확인했다. 변경하지 않은 NTT
전체를 이번 단계에서 중복 실행한 것으로 기록하지 않는다.

`CDTGaussianApproximation.uniform83_jasmin_half_gaussian_error`는 균등하게 뽑은
83비트 입력을 실제 `SamplerTarget.M.sample_gauss83_jazz`에 전달하는 실험을
다룬다. 목표는 `P(k)=exp(-k²/512)/sum_{j≥0}exp(-j²/512)`, `k≥0`이다.
구현과 무관하게 정의한 이 무한 분포와 실제 출력 분포의 통계적 거리가
**2^-78보다 작음**을 증명했으며, 모든 출력 집합의 확률 차이도 같은 상한을 갖는다.
정규화·무한 꼬리·지수함수 구간·수치 인증서를 가정으로 남기지 않고 검증했다.
공식 PDF와 참고문헌의 출처·수식 대응은
[별도 기록](docs/cdt-distribution-correspondence.md)에 있다.

`ApproxExpNumericalCorrectness.sigma76_approx_exp_numerical_total`은 모든 26바이트
입력에서 실제 인자 `xi`가 검증 구간 안에 있음을 해소하고, 실제 signer의
정규화 출력과 `exp(-uint(xi)/2^48)` 사이 오차≤27/2^48<2^-43을 증명한다.
계수 다항식의 격자 오차≤24/2^48과 실행 중 올림 오차≤3/2^48을 합쳤다.
모든 Horner prefix와 올림 곱셈 결과의 signed64 해석도 정당화했다.

`SigmaExpAcceptanceCorrectness`는 거부 바이트만 균등하게 바꾼 실제 sigma
호출의 승인 확률을 비교한다. 포화·even 비교·실제 rounded-zero 보정을 포함한
정확한 확률 공식과 실수 지수함수 기준 오차≤α·28/2^48<2^-43을 증명했다.
이는 실제 양자화된 지수와 반올림된 zero 규칙을 유지하는 조건부 정리다.
수식·출처·실제 프로시저 연결은 [수치 증명 기록](docs/approx-exp-mathematical-bound.md)에 있다.

`SigmaRawExponentCorrectness.sigma_raw_exponent_exact`는 실제 xi가
`floor((y(y+2^73x)+2^104)/2^105)`임을 증명한다. `SigmaSquareExact`가
해소한 정확한 제곱 정수식과 byte/CDT 범위를 사용하므로, 최종 26바이트
정리에는 추가 fit 전제가 없다. 정규화된 지수 오차는 2^-49 이하이며,
`SigmaRawDensityIdentity`는 비교 지수가 Gaussian 비정규화 가중치의 비율임을
증명한다.

`SigmaRawZeroCorrectness`는 두 0 검사 규칙이 달라지는 구간을 정확히
증명한다. 고정 후보에 대한 오차에는 그 예외의 반 보정이 남는다.
`SigmaRawAverageCorrectness.sr_average_acceptance_error_strict`는
`SigmaNoise72Experiment`가 독립적인 균등 72비트 잡음과 48비트 거부 난수를
실제 추출 프로시저에 전달했을 때, 반올림 전 Gaussian 수락식의 평균과 실제
승인 확률의 차이가 29/2^48 미만이며 2^-43 미만임을 증명한다.
CDT 입력은 고정되어 있으며 구체적 SHAKE의 균등성을 요구하지 않는다.
이는 단일 시도의 평균 승인 확률 정리다. 승인 후 조건부분포는 후속 정규화 정리에서 별도로 비교했다.
자세한 수식과 출처는 [반올림 전 수락식 연결](docs/raw-gaussian-acceptance.md)에 있다.

`SigmaJointCorrectness.sj_joint_output_error_strict`는 실제
`SigmaJoint203Experiment`와 독립적인 `SigmaJointIdeal`의 사건
`accepted /\ S(output)`을 모든 정수 출력 집합 S에 대해 비교한다.
차이는 29/2^48+2^-78 미만이고, 30/2^48 및 2^-43보다도 작다.

실제 표본은 W64의 unsigned 값으로 읽는다. 이상적 CDT는 모든 비음수
정수의 Gaussian이며, 이상적 반올림 값은 64비트로 감지 않는다. 구현 오차에는
먼저 출력 집합의 지시함수를 곱한 뒤 잡음을 평균하고, 그다음 [0,1] 커널의
기댓값 차이를 CDT 통계적 거리로 제한한다. 이 순서로 이상적 무한 꼬리에
구현의 x≤166 범위 가정을 적용하지 않는다. 승인 확률로 나누지 않은 결과이며,
승인 후 조건부분포는 아래 정규화 정리로 연결했고, 독립 난수의 거부 반복은 후속 정리에서 다룬다.
자세한 실험·수식·증명 연결은 [공동 출력 확률 기록](docs/joint-accepted-output.md)에 있다.

`SigmaAcceptanceLowerBound`는 후보의 CDT·잡음 바이트를 고정하고 거부 48비트를
균등하게 새로 뽑는 확률이 1/7 이상임을 증명한 뒤, 72·83비트 평균으로 실제
전체 실험의 같은 하한을 얻는다. 이상적 실험에는 공동 확률 오차로 하한 1/8을
전달하므로, 구현의 유한 지수 범위를 이상적 무한 꼬리에 적용하지 않는다.

`SigmaConditionalCorrectness.sc_conditioned_distributions_correct`는 실제 및
이전 독립 이상적 실험을 각자의 승인 사건으로 조건화한 native 정수 분포가
모두 질량 1임과 통계적 거리<2^-39를 증명한다. 두 분모가 다를 수 있음을
유지하고, 분자·분모 오차를 함께 반영한 16·(29/2^48+2^-78) 공통 상한을
모든 사건에 먼저 적용한 뒤 통계적 거리로 넘긴다. 양수성 전제는 최종 정리에서
모두 해소한다. 그 단계의 목표는 기존 이상적 실험의 조건부분포였으며, 아래
후속 정리에서 명시적인 Gaussian 반올림 확률 질량식과 식별했다.
자세한 분포·수식·검증 범위는 [조건부분포 기록](docs/conditional-accepted-output.md)에 있다.

`Gaussian76Properties`는 rho(k)=exp(-k²/2^153), k∈Z의 합 Z가 수렴하고
Z≥1임을 기하급수 상계로 증명한다. 정규화 분포의 질량은 1이며 모든 정수에
양의 확률을 갖는다. Z는 수락 확률이나 구현 테이블에서 정의하지 않았다.

`Gaussian76Identification.g76_ideal_conditioned_eq`는 기존 이상적 조건부분포가
G의 절댓값을 (|G|+32768) div 65536으로 반올림한 분포와 정확히 같음을 증명한다.
몫·나머지에 의한 무한 합 재색인, 모든 x≥0의 Gaussian 가중치 상쇄, 0을 한 번
계산하는 대칭 접기와 Z/(2·N·H16) 수락 확률을 합성했다. `g76_actual_gaussian_correct`는
실제 승인 표본 크기와 이 명시적 목표의 질량 1 및 통계적 거리<2^-39를 전달한다.
새 근사 오차는 추가되지 않는다.

`Gaussian76Rounding.g76_rounded_mass`는 각 이상적 출력값의 확률을 해당
반올림 구간의 Gaussian 가중치 유한 합으로 정확히 표현한다.
`g76_actual_rounded_mass_error`는 실제 승인 후 해당 값의 확률과 그 식 사이의
차이가 2^-39 미만임을 증명한다.
0은 |G|≤32767을 포함하며 ±32768은 모두 1로 간다. 이는 수학적 절댓값 분포의
식별이다. 이 식별 정리만으로 실제 부호 처리나 거부 반복을 증명한 것은 아니며, 반복은 후속 정리에서 다룬다.
정확한 질량식과 범위는 [Gaussian 식별 기록](docs/gaussian-magnitude-identification.md)에 있다.

`GaussianRetryActual.gr_actual_retry_ll`과 `gr_actual_retry_law`는 매번
실제 추출 시도를 호출하는 독립 난수 반복문의 확률 1 종료와 정확한 조건부분포를
증명한다. 새 오차 없이 Gaussian 거리<2^-39를 유지한다.
`GaussianRetryBatchCorrectness.gra_batch_joint_law`는 전체 승인 목록의 법칙을
`dlist(sc_actual_conditioned p,n)`으로 식별한다. 257번째 값을 먼저 생성한 뒤
앞 256개를 취하는 프로시저도 확률 1로 종료하며 앞 256개의 분포를 보존한다.

`GaussianRetryInputs`는 canonical 203비트를 담은 26바이트 후보를 연속
후보 스트림과 연결한다. 사용하지 않는 상위 5비트는 0이다.
`GaussianRetryPrefixCorrectness`는 실제 버퍼 증명의 `gr_adequate` 조건과
같은 부족 사건을 사용하여 n·t개 후보에서 부족 확률≤n·(6/7)^t와 모든 후보·블록
길이에서의 부족 확률→0을 증명한다. 무한 균등 함수 분포를 도입하지 않았다.

`GaussianRetryStreamTermination.gr_sample_gauss_N_prefix_total`은 요청
256/257, 기존 offset·초기 limb 범위와 구체적 SHAKE 스트림의 충분한 유한 구간
전제 아래 실제 `_sf_sample_gauss_N_full_at`의 종료와 접두 구간 명세를 증명한다.
유한 범위 안의 최대 호환 블록 번호로 감소량을 정의하므로 SHAKE 상태와 블록
번호가 일대일이라는 가정도 필요하지 않다. 32바이트 부호, 앞 256개 출력,
257번째 dummy를 포함한 정수 제곱 limbs 합과 외부 영역 보존을 유지한다.
이 결과는 명시적인 iid 바이트 공급 버퍼 드라이버의 확률 법칙이나
구체적 SHAKE의 독립성·모든 seed의 종료 증명이 아니다.
[반복·목록·버퍼 범위](docs/gaussian-retries-and-batches.md)에 구분과 정리 지도를 기록했다.

`GaussianStreamCorrectness.sample_gauss_N_full_at_correct`는 실제
`_sf_sample_gauss_N_full_at`의 seed·nonce 초기화, 49블록, 부호 복사, 반복
carry/refill/소비를 모두 포함한다. 요청 256/257, 유효 offset, 초기 두 limb
`<2^48`에서 **종료한 실행의 반환 튜플**이 명세와 일치한다. 명세 결과의 유일성도
검사했다. 고정 seed의 무조건 종료를 가정하지 않았다. 앞선 Hyperball 단계에서는
강화한 square-high 상한 `<2^36`과 최대 2,818개 승인 후보의 누적 예산으로
여러 polynomial 호출 사이의 초기 두 limb 조건도 증명했다.

`HyperballCorrectness.hyperball_full_correct`와 `hyperball_mode{2,3,5}_correct`는
실제 `_sf_hyperball_full`과 세 wrapper의 **종료한 실행이 정확한 word 명세와
일치함**을 증명한다. 모든 Gaussian 호출, 초기 추정과 Newton 6회 갱신,
좌표별 sign/scaling, 모듈러 norm, 이전 시도의 거부와 마지막 승인,
최종 SHAKE 바이트와 카운터를 포함한다. scratch 미사용 영역이나 충분한
스트림 prefix의 선택에 관계없이 반환값이 유일함도 증명했다.

norm 승인은 signed32 좌표의 정수 제곱합 `N`에 대한 `N mod 2^64 <= bound`다.
정수 반경 보장은 `N < 2^64` 또는 명시적 좌표 범위 아래에서만 도출했다.
고정 후보열의 C/Jasmin 재현은 wrap 이후 norm 검사 통과를 확인하지만,
그 후보열을 생성하는 실제 SHAKE seed의 존재나 구체적 seed 반례를 주장하지 않는다.
수치와 재현 명령은 [수치 경계](docs/hyperball-numerical-boundary.md)에 기록했다.

실행 기록은 `logs/latest-generated.json`, `logs/latest-new.json`과 각각의
실행별 하위 디렉터리에 있다. 같은 작업에서 실행한 NTT 개별 로그는
`logs/ntt-support-replay/`에 보존했다. 로그는 생성물이므로 Git에서 제외한다.
소스와 도구 식별자는 `manifests/`에서 확인할 수 있다.

## 재현 명령

```sh
# 전체 범위의 새 검증
make -C haetae-1.2.0-easycrypt verify

# 그룹별 동일 검증
make -C haetae-1.2.0-easycrypt verify-generated
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt verify-ntt
make -C haetae-1.2.0-easycrypt test-gate
make -C haetae-1.2.0-easycrypt test-hyperball-boundary
```

전체 검증에는 시간이 큰 NTT 유한표와 루프 증명도 포함된다. 세 그룹을 별도로
실행한 결과를 합칠 때에는 소스·추출물·도구 버전이 동일한지 확인해야 한다.

## 검증 절차 자체의 확인

- 60개 Jasmin 소스·헤더·빌드 입력과 생성된 파일 102개의 해시를 고정했다.
- 재추출 결과 전체와 저장된 추출물이 일치했고, 중복 이름의 배열 이론 21종도
  내용이 일치했다.
- C에서 독립적으로 생성한 CDT·다항식 상수는 재생성 결과가 일치했다.
  C 사본의 CDT 항목 및 다항식 계수를 바꾼 두 음성 검사는 각각 인증 정리에서
  실패했다.
- Hyperball의 mode별 상수는 고정 C의 실제 표현식을 컴파일하여 독립 생성했다.
  GCC 11.4와 Clang 14의 결과가 바이트 단위로 일치했고, 최종 게이트에서도
  재생성 일치를 확인했다. 생성 이론의 scale 상수 한 자리를 바꾸는 음성 검사로
  provenance 게이트의 거부를 확인했다. 테스트는 실제 파일을 수정하지 않는다.
- 새 Gaussian 인증서는 정수 구간 연산으로 재생성하고 저장된 내용과 비교했다.
  EasyCrypt에서 외향 반올림 연산의 실수 포함 관계와 모든 필요한 수치 부등식을
  검사했다. 제곱 단계 또는 비교 대상 CDT 값 하나를 바꾼 임시 인증서는 실제
  검사 정리에서 실패했고, 변경하지 않은 대조군은 통과했다. 임시 모듈 이름과
  데이터 식별자를 분리하여 원본 명세가 대신 로딩되는 경우를 방지했다.
- 지수함수 인증서는 정확한 유리수 연산으로 재생성했다. 독립 구현에서도 같은
  66개 정수 제어 계수를 얻었다. EasyCrypt는 기저 변환·비음수성뿐 아니라 실제
  다항식과의 여섯 항등식도 검사했다. 음수 제어 계수, 내부적으로 일관되지만
  다른 다항식을 나타내는 양수 인증서, 변경된 참조 계수는 모두 실패했다.
  정상 대조군은 통과했고 실제 파일은 변경하지 않았다.
- 증명 게이트가 `Proofs:weak`, `Proofs:report`, 미완성 증명, 새 공리와
  허용되지 않은 constrained declaration을 거부함을 확인했다. NTT 예외는
  이름과 해시로 고정한 특정 지원 파일에만 적용한다.
- source drift 등 사전 검사 실패 시 이전 PASS 기록이 남지 않고 최신 기록이
  FAIL로 바뀌는 경우를 확인했다.
- EasyCrypt가 열린 증명·누락된 `qed`·미해결 clone 의무의 EOF에서 성공 코드를
  반환하는 경우를 재현했다. 동일 basename의 임시 복사본에 마지막 확인 정리를
  붙여 이 경우를 거부한다. 정상 증명·inline 증명·clone/realize는 통과하고,
  입력 원본·종료 코드·임시 파일 정리도 회귀 테스트로 확인했다.
- SHAKE 지원에 사용한 과거 파일 4개의 해시가 보존된 Git 스냅샷과 일치했다.
  가져온 부분은 현재 서명 추출물에 맞춰 수정하고 두 로컬 파일을 모두 새로 검증했다.
- 고정된 공식 C 배포본, 생산 Jasmin 소스 및 `archive` 자료를 변경하지 않았다.

독립 검토에서 실제 production 문맥 helper의 연결과 rounded 결과의 정수 의미
연결 부족을 발견하여 각각 `ProductionApiCorrectness`와
`SigmaRoundingCorrectness`로 보완했다. 최종 검토는 현재 구성요소 범위를 승인했다.
Hyperball 단계의 독립 검토는 실제 전체 함수·mode wrapper의 word 부분
정확성 범위를 승인했다. 여러 Gaussian 호출의 전제, 실제 고정소수점·scaling·norm
호출, 최초 승인 이력, 최종 byte/counter와 반환값 유일성을 확인했다. 공개 정리의
전제에 원하는 결론·수치 fit·수렴·종료 가정을 숨기지 않았음을 확인했다.
수학적 norm의 무조건 보장, 실수 Newton 수렴·오차, 확률 분포·종료성,
FIPS bit 명세의 별도 동치, 전체 API 합성은 남은 의무다.

CDT 단계의 최종 독립 검토는 공식 출처의 비음수 Gaussian 정의, 무한 정규화와
꼬리, 구간 인증서, strict 비교의 +1 경계, 실제 Jasmin 호출, 통계적 거리의 1/2
계수, 임의 출력 집합에 대한 정리를 확인했다. 최종 변조 테스트의 이름 분리와
정상 대조군도 별도로 검토했다. 승인은 단일 CDT의 명시적 균등 입력 실험에
한정한다. 공식 명세의 별도 Rényi 경계, sigma76 거부 샘플링, 실제 SHAKE
균등성·독립성, Hyperball 및 전체 서명 분포까지 확대하지 않는다.

지수함수 단계의 독립 검토는 실제 입력 범위와 signed Horner 해석, 24+3 오차
합성, 실제 호출의 종료성, 조건부 sigma 호출과 clipped/even 승인식을 확인했다.
그 단계의 비교 대상은 `α(actual rounded)·exp(-actual xi/2^48)`이다.
후속 단계에서 raw 지수의 오차와 두 zero 규칙의 차이를 증명하고, 명시적인
균등 잡음으로 평균한 승인 확률까지 연결했다. 단방향 ceiling, 공식 Rényi
경계와 전체 Gaussian 출력 분포는 여전히 별도 의무다.

## 판정의 의미

이 기록은 [CLAIMS.md](CLAIMS.md)에 등록된 구성요소 정리의 통과 기록이다.
생성 파일 102개의 검사 수를 기능 정확성 정리 102개로 계산하지 않는다.
전체 KeyGen/Sign/Verify, 구체적 SHAKE·Hyperball 실행의 무조건 종료·분포, Sign→Verify 합성,
운영체제 메모리 접근이나 생성 어셈블리의 전체 정확성은 미완료다.
NTT의 산술 가정은 [가정 목록](manifests/ntt-assumptions.md)에 남아 있다.

반올림 전 수락식 단계의 독립 검토는 정확한 제곱·지수 식, Gaussian 가중치
비율, 두 0 규칙의 예외 구간, 실제 72+48비트 확률 실험과 평균 합성을 확인했다.
모든 고정 후보의 작은 오차로 과장하지 않고 예외를 명시했으며, 승인 후 조건부분포·거부
정규화·공식 Rényi 경계·구체적 SHAKE·전체 API는 남은 의무로 유지한다.

공동 출력 단계의 독립 검토는 실제 unsigned 반환값, 모든 출력 집합의 사건,
독립적인 83+72+48비트 실험, 무한 Gaussian 지지집합과 무제한 정수 반올림,
지시함수를 적용한 점별 오차, 계수 1의 CDT 커널 수축과 최종 수치를 확인했다.
당시 정리에 fit·정확도·출력 집합 제한을 숨기지 않았고, 승인 후 정규화나
실제 SHAKE 성질을 그 공동 확률 결과로 주장하지 않았음을 확인했다.

조건부분포 단계의 독립 검토는 실제·이상적 native 분포와 프로그램 확률의 연결,
구별된 분모, 수치 승인 하한과 최종 양수성 전제 해소, 질량 1, 모든 사건의 공통
비엄격 오차 상한을 통한 엄격 통계적 거리 경계를 확인했다. 기준 분포는 이전
이상적 실험에 승인 조건을 붙인 것이며, 당시에는 별도 Gaussian 질량식 식별·부호·거부
반복·실제 SHAKE를 그 조건부분포 결과로 주장하지 않았음을 확인했다.

Gaussian 식별 단계의 독립 검토는 독립적인 모든 정수의 정규화, 절대수렴에
근거한 제한된 몫·나머지 재색인, 이상적 x의 무한 범위, Z/2의 0 보정 계수,
절댓값을 먼저 적용하는 반올림과 정확한 조건부분포 등식을 확인했다.
실제 분포의 기존 오차는 그 등식만으로 이전하며, 실제 부호·반복·SHAKE나
전체 API 정확성을 추가로 주장하지 않음을 확인했다.
