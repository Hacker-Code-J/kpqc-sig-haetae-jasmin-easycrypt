# 검증 기록

2026-09-17~18 작업에서 현재 Jasmin 소스로 재추출하고 EasyCrypt를 실제 실행했다.
기존 버전의 검증 로그나 KAT 결과를 새 증명의 근거로 대체하지 않았다.

| 구분 | 새로 검사한 대상 | 결과 |
| --- | --- | --- |
| 추출물 | 배열 이론과 현재 프로그램 102개 | 모두 PASS |
| 새 명세·증명 | `verify-new`의 27개 파일 | EOF 확인을 포함한 새 통합 실행 모두 PASS |
| NTT | 필요한 지원 이론 11개와 현재 구현 정리 1개 | 각 파일을 주 대상으로 실행하여 모두 PASS |
| 검증기 회귀 | 미완성 EOF 거부·정상 증명·임시 파일·종료 코드 10개 테스트 | 모두 PASS |

전체 로컬 명세·증명 39개를 각각 주 검증 대상으로 검사했다. import만 된 증명의
본문이 자동으로 재검사된다고 가정하지 않았다. 새 코드 게이트는 `-no-eco`와
명시적 `Proofs:check`를 사용하며, 원래 NTT 지원 재검증도 `-no-eco`의 기본
강한 검사 모드로 개별 실행했다.

이번 단계에서는 정확한 Gaussian trace·승인 순서·제곱합·서명 offset 연결·carry·
SHAKE 단일 블록을 추가했다. 새 그룹 27개 파일의 최종 통합 검증 시간은 약
436초였다. 기존 NTT 12개와 추출물 102개는 이전 새 검증 결과를 보존하고,
해시 불변 및 현재 소스의 재추출 일치를 다시 확인했다. 변경하지 않은 NTT
전체를 이번 단계에서 중복 실행한 것으로 기록하지 않는다.

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
이번 단계의 별도 의미 검토에서도 dummy·거부 후보의 임시 쓰기·offset·정수
오버플로 전제에 문제가 없음을 확인했다. 호출 간 제곱합 범위와 전체 refill 반복문,
SHAKE 흡수·패딩·sponge, 전체 API 합성은 남은 의무로 유지한다.

## 판정의 의미

이 기록은 [CLAIMS.md](CLAIMS.md)에 등록된 구성요소 정리의 통과 기록이다.
생성 파일 102개의 검사 수를 기능 정확성 정리 102개로 계산하지 않는다.
전체 KeyGen/Sign/Verify, 전체 거부 루프·분포, Sign→Verify 합성,
운영체제 메모리 접근이나 생성 어셈블리의 전체 정확성은 미완료다.
NTT의 산술 가정은 [가정 목록](manifests/ntt-assumptions.md)에 남아 있다.
