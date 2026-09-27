# Gaussian 거부율과 평균 후보 시도 횟수

독립 균등 난수를 공급한 **실제 Jasmin Gaussian 후보 한 번의 거부 확률은 5% 미만**이다.
성공할 때까지 같은 방식으로 새 후보를 만드는 모형에서, 성공한 후보까지 포함한
시도 횟수 `T`의 평균은 **`E[T] < 20/19 ≈ 1.052632`**다.

| 수치 | 의미와 출처 |
| --- | --- |
| 거부 확률 `< 1/20` | [HAETAE 명세 260904 §5.1.1](https://drive.google.com/file/d/1H2SFqZFG5BcWH--bJKssvXaSG0Sd3mUx/view)의 Gaussian 거부율 `<5%`에 대응한다. |
| 평균 시도 횟수 `< 20/19` | 실제 승인 확률 `p > 19/20`와 재시도 횟수 법칙에서 이번에 유도한 상한이다. 명세에서 인용한 수치는 아니다. |
| 이상적 승인 확률 `≥ 39/41` | 실제 구현과 비교하는 이상적 후보 실험의 증명용 하한이다. 측정된 승인율을 뜻하지 않는다. |

한 번의 시도는 `__sample_gauss_sigma76_regs`에 26바이트 후보 하나를 전달하는
것이다. CDT에 쓰는 83비트, 추가 잡음 72비트, 거부 판정 48비트가 서로 독립이고
균등하다. 26바이트 전체를 균등하게 뽑아도, 사용하지 않는 5비트가 결과에 영향을
주지 않아 같은 법칙을 얻는다.

5% 경계는 이 입력들을 모두 평균한 결과다. CDT 값과 잡음 값을 고정한 뒤에도
각 후보의 승인 확률이 95% 이상이라는 주장은 아니다. `T`에는 첫 시도와 마지막
성공 시도를 모두 포함한다. SHAKE 블록 수, 버퍼 refill 횟수, 더미를 제외한
배치 출력의 비용, Hyperball 전체 재시도 횟수와는 다른 양이다.

## 증명의 연결

1. 기존 유리수 인증서에서 sigma 16 비음수 Gaussian의 정규화 상수
   `H ≥ 41/2`를 얻는다. `H`는 0의 가중치를 1로 계산한다.
2. Gaussian 질량의 단조성과 기존 격자 합 정리를 이용해 이상적 승인 확률이
   `p_ideal ≥ 1 − 1/H ≥ 39/41 > 951/1000`임을 증명한다. raw 후보 0의 반 가중치를
   유지하며, Gaussian 적분이나 새 수치 가정을 도입하지 않는다.
3. 기존에 증명한 실제·이상적 승인 확률 차이 `< 2^-43`을 적용한다.
   따라서 `p > 951/1000 − 2^-43 > 19/20`이고 거부 확률은 `< 1/20`이다.
4. 실제 추출 함수를 호출하는 반복문에 분석용 정수 계수기를 추가한다.
   계수기를 지워도 기존 IID 후보 반복모형의 출력이 같음을 연결하고, 실제 횟수의
   분포·기대값의 유한성·`E[T] = 1/p`를 증명해 `< 20/19`를 얻는다.

`GaussianAcceptanceProduction`은 새로 추출한 서명용·독립 Hyperball 코드의
Gaussian 함수를 직접 호출한다. `GaussianProductionCounted`는 같은 함수를 매번
새 균등 26바이트로 호출하며 실제 시도 횟수를 센다. 함수 본문의 대응은
EasyCrypt 관계적 동치로 검사한다.

확률 모형에는 구체적인 SHAKE 실행을 대신해 독립 균등 입력을 명시했다.
Gaussian 후보 반복문의 종료는 이 모형에서 확률 1로 성립한다. 구체적 SHAKE와의
보안 가정 연결, Hyperball 외부 반복문의 종료, 공식 Rényi 경계, 전체 API 정확성은
별도 과제다. C/Jasmin 실행 코드는 이 단계에서 변경하지 않았다.

## 파일과 재현

| 파일 | 검증 대상 |
| --- | --- |
| `GaussianAcceptanceConstants.ec` | 기존 인증서로부터 필요한 정규화 상수와 수치 여유 도출 |
| `GaussianAcceptanceIdeal.ec` | 이상적 승인 확률의 해석적 하한 |
| `GaussianAcceptanceActual.ec` | 실제 승인·거부 확률 및 연속 거부 꼬리 상계 |
| `GaussianAcceptanceProduction.ec` | 실제 생산 코드와 균등 26바이트 실험의 연결 |
| `GaussianAttemptExpectation.ec` | 후보 횟수를 세는 반복문, 횟수 분포와 유한 평균 |
| `GaussianAttemptProduction.ec` | 생산 코드 후보 반복문에 같은 횟수·평균 결과 연결 |

각 파일은 [easycrypt/proofs](easycrypt/proofs/)에 있다. 저장소 루트에서:

```sh
make -C haetae-1.2.0-hardened prepare
python3 haetae-1.2.0-hardened/tests/gaussian-rate-gate.py
python3 haetae-1.2.0-hardened/scripts/verify.py --group gaussian-rate
```

이미 실행 중인 Why3 서버를 이용하려면 `WHY3_SERVER_SOCKET`을 설정한다.
새 정리와 가져오는 로컬 의존 정리를 각각 main target으로 재검사하며,
`-no-eco`, `Proofs:check`, EOF 완결성 검사를 적용한다. 새 추출 결과의 일치와
기존 파일 해시도 확인한다. 정확한 대상·해시·결과는
[gaussian-acceptance-results.json](gaussian-acceptance-results.json)에 기록한다.
이전 보강안의 [KAT·실행 검사 기록](verification-results.json)은 당시 검증기와
대상 목록의 해시를 포함한 역사 기록으로 보존한다. 이번에 변경한 검증기·목록과,
그대로 유지한 실행 코드·런타임 산출물의 해시 대조 범위는 새 기록에 명시한다.
