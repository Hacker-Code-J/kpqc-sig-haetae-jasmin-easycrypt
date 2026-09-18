# 검증 기록

2026-09-17~18 작업에서 현재 Jasmin 소스로 재추출하고 EasyCrypt를 실제 실행했다.
기존 버전의 검증 로그나 KAT 결과를 새 증명의 근거로 대체하지 않았다.

| 구분 | 새로 검사한 대상 | 결과 |
| --- | --- | --- |
| 추출물 | 배열 이론과 현재 프로그램 102개 | 모두 PASS |
| NTT 외 명세·증명 | `verify-new`의 51개 파일 | EOF 확인을 포함한 새 통합 실행 모두 PASS |
| NTT | 필요한 지원 이론 11개와 현재 구현 정리 1개 | 각 파일을 주 대상으로 실행하여 모두 PASS |
| 검증기 회귀 | 미완성 EOF 거부·정상 증명·임시 파일·종료 코드 10개와 Hyperball 상수 drift 1개 | 11개 모두 PASS |
| Hyperball 수치 재현 | mode 2·3·5의 고정 후보열을 C/Jasmin으로 실행 | 정확한 word 결과·모듈러 norm 승인 일치, 정수 norm 초과 재현 |

전체 로컬 명세·증명 63개를 각 단계에서 주 검증 대상으로 검사했다. import만 된 증명의
본문이 자동으로 재검사된다고 가정하지 않았다. 새 코드 게이트는 `-no-eco`와
명시적 `Proofs:check`를 사용하며, 원래 NTT 지원 재검증도 `-no-eco`의 기본
강한 검사 모드로 개별 실행했다.

이전 단계의 전체 Gaussian·연속 word SHAKE 스트림 증명에 이어, 이번에는
16개 명세·증명 파일을 추가해 실제 전체 Hyperball 함수와 세 mode wrapper를
검증했다. 51개 파일의 최종 통합 검증 시간 합계는 약 1,053초였다.
기존 NTT 12개와 추출물 102개는 이전 새 검증 결과를 보존하고,
해시 불변 및 현재 소스의 재추출 일치를 다시 확인했다. 변경하지 않은 NTT
전체를 이번 단계에서 중복 실행한 것으로 기록하지 않는다.

`GaussianStreamCorrectness.sample_gauss_N_full_at_correct`는 실제
`_sf_sample_gauss_N_full_at`의 seed·nonce 초기화, 49블록, 부호 복사, 반복
carry/refill/소비를 모두 포함한다. 요청 256/257, 유효 offset, 초기 두 limb
`<2^48`에서 **종료한 실행의 반환 튜플**이 명세와 일치한다. 명세 결과의 유일성도
검사했다. 고정 seed의 무조건 종료를 가정하지 않았다. 이번 Hyperball 단계에서는
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
이번 단계의 독립 검토는 실제 Hyperball 전체 함수·mode wrapper의 word 부분
정확성 범위를 승인했다. 여러 Gaussian 호출의 전제, 실제 고정소수점·scaling·norm
호출, 최초 승인 이력, 최종 byte/counter와 반환값 유일성을 확인했다. 공개 정리의
전제에 원하는 결론·수치 fit·수렴·종료 가정을 숨기지 않았음을 확인했다.
수학적 norm의 무조건 보장, 실수 Newton 수렴·오차, 확률 분포·종료성,
FIPS bit 명세의 별도 동치, 전체 API 합성은 남은 의무다.

## 판정의 의미

이 기록은 [CLAIMS.md](CLAIMS.md)에 등록된 구성요소 정리의 통과 기록이다.
생성 파일 102개의 검사 수를 기능 정확성 정리 102개로 계산하지 않는다.
전체 KeyGen/Sign/Verify, 거부 루프의 무조건 종료·분포, Sign→Verify 합성,
운영체제 메모리 접근이나 생성 어셈블리의 전체 정확성은 미완료다.
NTT의 산술 가정은 [가정 목록](manifests/ntt-assumptions.md)에 남아 있다.
