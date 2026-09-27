# Hyperball 한 번의 시도에 대한 지수근사 Rényi 경계

독립 균등 바이트 모형에서 **실제 정수 지수근사를 사용하는 Hyperball 한 번의 시도**와
**Gaussian 승인 확률만 정확한 exp로 바꾼 기준 시도**를 비교한다.
관측값은 두 출력 배열과 승인/거부 비트다. 거부된 후보도 포함한다.
nonce, 소비한 난수의 수와 마지막 추가 출력 `b`는 이 관측에 포함하지 않는다.

정수 차수 `2 ≤ α ≤ 1024`에서 양방향 모두 다음 상한을 증명한다.

```text
R_α(실제 시도, 정확한 exp 기준 시도) ≤ (1 + 2^-68)^D < 1 + 2^-56.
```

| 모드 | 가시 계수 | 제곱합에만 포함되는 더미 | 전체 Gaussian 표본 D |
| --- | ---: | ---: | ---: |
| 2 | 1,536 | 2 | 1,538 |
| 3 | 2,304 | 2 | 2,306 |
| 5 | 2,816 | 2 | 2,818 |

여기서 Rényi 값은 [앞선 단일 Gaussian 증명](gaussian-renyi.md)과 같은 **비로그**
정의다. `2^-56`은 이 값의 1 초과분에 대한 공통 상한이며, 통계적 거리나
실측 오차 또는 보안 비트 수가 아니다. 모드별 거듭제곱 상한도 별도로 유지한다.

## 비교에서 유지하는 것과 바꾸는 것

실제 시도와 기준 시도는 같은 유한 CDT, 72비트 잡음, 양자화된 지수,
반올림된 0의 승인 보정과 출력 반올림을 사용한다. 기준 시도에서는 실제 정수
지수근사와 48비트 승인 문턱 대신 정확한 `exp(-X/2^48)` 승인 확률을 사용한다.
48비트 거부 난수는 먼저 평균하여 승인 커널에 포함한다.

그 이후의 부호, raw 제곱 누적, Newton 역제곱근, 고정소수점 곱셈, 계수 변환,
하드닝된 overflow 검사와 승인 판정은 양쪽에서 같다. 이 단계는 해당 exp 교체의
영향을 측정하며, 그 모든 계산을 이상적 실수 산술로 교체하지 않는다.

Gaussian 한 표본은 반올림 크기와 raw 제곱 두 limb를 함께 보존한다. 내부 S는
반올림된 출력 계수의 제곱합이 아니다. 첫 두 호출의 257번째 승인 표본은 배열에
저장되지 않지만 S에 더해진다. 두 더미 모두 분포 합성의 D에 포함한다.

## 실제 실행과의 연결

- `HyperballRenyiPayload`: 실제 승인 payload의 분포를 기존 `gpd_accepted`와
  동일시하고, 크기와 raw 제곱을 함께 유지한 단일 표본의 Rényi 경계를 증명한다.
- `HyperballRenyiProduct`·`BatchBounds`: 곱분포의 Rényi 값이 곱해짐을 증명한다.
  각 호출의 독립 32바이트 부호는 추가 오차를 만들지 않는다. `1+Dε`로 대체하지
  않고 정확한 거듭제곱을 유지하여 공통 상한을 도출한다.
- `HyperballRenyiBuffer`·`Schedule`·`Joint`: 실제 sign-copy·carry·유한 소비기의
  반환 상태와 독립 payload·부호 블록에서 복원한 전체 표본·부호·제곱 배열을 연결한다.
  부호와 제곱합의 독립성을 가정으로 추가하지 않는다.
- `HyperballRenyiHardened`: 새 하드닝 추출 모델의 Gaussian helper들과 앞서 검증한
  버퍼 모델 사이의 전체 반환 상태 동일성을 증명한다.
- `HyperballRenyiArithmetic`: 실제 하드닝된 산술 helper들이 정확히 어떤 배열과
  승인 비트를 반환하는지 증명한다. 안전 구간·fit·무overflow를 전제하지 않는다.
- `HyperballRenyiMap`·`Production`: 동일한 후속 계산에서 Rényi 값이 증가하지
  않음을 적용하고, 실제 시도와 기준 실행을 각각 명시한 분포에 연결한다.

`hrf_attempt_law`와 `hrf_exact_law`가 두 실행의 분포를,
`hrf_renyi_bounds`와 `hrf_common_bound`가 누적 상한을 진술한다.
명시적 iid 모형의 한 번의 시도는 양쪽 모두 확률 1로 종료한다.

이 실행 모형은 기존 iid 증명과 같은 0 초기 표본·부호·제곱 배열과 0 출력 scratch를
사용한다. 실제 추출 helper를 호출하지만 SHAKE 대신 독립 바이트를 공급한다.
임의 stack 전체의 분포, 임의 포인터의 메모리 안전성, 모든 seed의 행동을 주장하지 않는다.

## 재현과 남은 범위

```sh
make -C haetae-1.2.0-hardened prepare
python3 haetae-1.2.0-hardened/tests/gaussian-rate-gate.py
python3 haetae-1.2.0-hardened/tests/gaussian-renyi-gate.py
python3 haetae-1.2.0-hardened/tests/hyperball-renyi-gate.py
python3 haetae-1.2.0-hardened/scripts/verify.py --group hyperball-renyi
```

기존 Why3 서버를 쓰면 `WHY3_SERVER_SOCKET`을 설정한다. 새 파일과 로컬 의존 증명을
각각 fresh main으로 검사하며 추출 일치, EOF 완결성과 소스 해시를 확인한다.
대상별 결과는 [hyperball-renyi-results.json](hyperball-renyi-results.json)에 기록한다.

이번 단계에서는 C/Jasmin 실행 코드를 변경하지 않았다. 기존 KAT·API·CT/SCT 실행
기록은 변경되지 않은 구현의 해시와 함께 보존하며, 이번에 새로 실행한 증명·검증기
회귀 검사와 구분한다.

**Hyperball이 승인될 때까지 반복한 뒤의 최종 분포**는 후속 과제다. 승인 사건으로
조건화한 분포, 외부 재시도의 승인 확률·종료, 이상적 Gaussian 전체와의 Rényi 비교,
구체적인 SHAKE와 iid 모형의 연결, 전체 KeyGen/Sign/Verify 정확성 및 서명 질의 전체의
보안 합성도 이 결과에 포함하지 않는다.
