# HAETAE-1.2.0 Hyperball 산술 보강안

기존 HAETAE-1.2.0 Jasmin 구현을 보존하고, Hyperball의 계수 변환과 제곱합
오버플로를 검사하는 별도 구현이다. **보강안이 승인한 벡터의 실제 정수 제곱합은
모드의 상한 이하**라는 성질을 EasyCrypt로 검증한다.

후속 [Gaussian 거부율·평균 횟수 증명](gaussian-acceptance.md)은 독립 균등 난수
모형에서 실제 후보 거부 확률 `<5%`와 성공까지의 평균 후보 시도 횟수 `<20/19`를
연결한다. Hyperball 외부 재시도의 종료와 구분한다.

`N = Σ signed32(y1[i])² + Σ signed32(y2[j])²`에서 합과 제곱은 무제한 정수
계산이다. 검사 전에 `N < 2^64`나 Gaussian 입력의 안전 구간을 가정하지 않는다.

| 모드 | 검사하는 계수 수 | 정수 제곱합 상한 |
| --- | ---: | ---: |
| 2 | 1024 + 512 | 6,505,809,026,482,176 |
| 3 | 1536 + 768 | 22,510,896,139,993,088 |
| 5 | 1792 + 1024 | 33,503,371,683,954,688 |

상한은 보존한 1.2.0 구현의 상수다. 이 폴더의 이름은 공식 새 배포 버전을
뜻하지 않는다. 기존 구현과 동작이 달라지는 입력을 명시적으로 거부하는 연구용
보강안이며, 라이브러리 이름과 SONAME에도 `hardened`를 넣었다.

## 무엇을 검사하고 증명하는가

| 대상 | 성질 | 종료에 관한 범위 |
| --- | --- | --- |
| 스칼라 변환 | 마지막 반올림을 덧셈 넘침 없이 계산하고, 크기 `M > 2147483647`이면 실패 마스크를 반환한다. 저장되는 32비트 계수는 기존 구현과 같다. | 항상 종료 |
| 벡터 변환 | 두 배열을 처리하면서 실패를 누적한다. 승인되면 모든 활성 표본의 변환 전 크기가 `2147483647` 이하다. | 항상 종료 |
| 제곱합 | 반환 워드는 `N mod 2^64`이고, 오버플로 마스크가 0일 필요충분조건은 `N < 2^64`다. | 배열 길이 범위 안에서 정확하며 항상 종료 |
| 승인 판정 | 배열 길이 조건만으로 `accepted = 1 ⇒ N ≤ bound`다. 표본·부호·scale 배열은 임의다. | 유한 판정 함수는 항상 종료 |
| 실제 호출 경로 | 새로 추출한 서명용·독립 Hyperball·공개 phase 경로에 같은 판정 성질을 연결한다. | 전체 Hyperball은 **반환한 실행**에 대한 성질 |

증명 파일은 [easycrypt/proof-targets.txt](easycrypt/proof-targets.txt)에,
재실행 결과와 해시는 [verification-results.json](verification-results.json)에 있다.
과거 `ApiTarget`을 새 구현으로 바꾸지 않고, 새 생산 소스에서 별도
`HardenedSignerTarget`, `HardenedHyperballTarget`, `HardenedPhaseTarget`을 추출한다.

계수 변환 검사는 곱셈이 반환한 상위 워드 `r1`에 대해
`M = floor((uint64(r1) + 16384) / 32768)`를 검사한다. 이 마지막 덧셈은 정수
덧셈으로 해석한다. 그보다 앞선 고정소수점 곱셈과 Newton 단계는 기존 워드
계산을 유지한다. 따라서 모든 중간 계산이 실수 산술과 정확히 같다는 주장은 아니다.
검사는 부호에 관계없이 같은 상한을 사용하므로, 음수로는 표현 가능한
`M = 2^31`도 거부한다.

검사 루프는 끝까지 실행하고 실패 여부를 누적한다. 제곱합이나 내부 실패 마스크는
공개하지 않으며, 기존 재시도 흐름에 필요한 최종 승인 비트만 공개한다.
CT/SCT 검사는 이 명시적 공개 조건하에서 수행한다.

## 기존 동작과의 차이 및 실행 검사

기존에 구성한 모드 2·3·5 반례는 모두 기존 승인 `1`에서 새 거부 `0`으로
바뀐다. 출력 계수 워드는 같다. 테스트용 함수와 **각 모드의 실제 생산
라이브러리 공개 함수**에서 모두 확인한다. 이 반례에 대응하는 SHAKE seed가
존재한다거나 전체 서명 API에서 도달할 수 있다는 주장은 하지 않는다.

경계 검사는 계수 변환 실패와 노름 실패를 각각 독립적으로 유발한다. 예를 들어
크기 `2^30`인 계수 16개는 각각 32비트에 들어가지만, 제곱합은 정확히 `2^64`다.
누적 워드가 0으로 돌아와도 새 판정은 거부한다.

공식 KAT는 모드마다 100건씩 총 300건의 요청·응답 파일이 일치한다. API 경계,
서명·검증, C 참조 구현과의 상호운용 검사도 실행한다. KAT 통과만으로 모든 입력에서
기존 구현과 동등하다는 뜻은 아니며, 위 반례의 승인 결과는 의도적으로 다르다.

## 재현

저장소 루트에서 실행한다. 기존 환경의 Jasmin, EasyCrypt, C 컴파일러와 OpenSSL을 사용한다.

```sh
make -C haetae-1.2.0-jasmin -j1 libs
make -C haetae-1.2.0-hardened -j1 test
python3 haetae-1.2.0-hardened/tests/checked-hyperball.py
bash haetae-1.2.0-hardened/scripts/check-ct.sh
python3 haetae-1.2.0-hardened/tests/materialize.py
python3 haetae-1.2.0-hardened/tests/verification-gate.py
python3 haetae-1.2.0-hardened/scripts/verify.py
```

Why3 서버를 이미 사용하는 환경에서는 `WHY3_SERVER_SOCKET`을 설정할 수 있다.
검증기는 모든 새 증명과 그 증명이 가져오는 기존 로컬 증명을 각각 main target으로
검사한다. `-no-eco`, `Proofs:check`, EOF 완결성 검사를 사용하며 프로젝트 axiom,
admit, 검증 우회 pragma를 허용하지 않는다. 그 밖의 기존 증명은 해시로 보존하며,
이번에 다시 검사한 범위와 구분한다.

정리는 Jasmin의 `barray` 추출 모형에 대한 것이다. 실제 호출의 배열 크기·포인터
계약과 도구 체인은 신뢰 경계에 남으며, 임의 포인터 사용의 메모리 안전성까지
증명한 것으로 해석하지 않는다.

[baseline-lock.json](baseline-lock.json)은 기준 커밋의 원본 Jasmin·EasyCrypt·참조
구현·archive 파일 542개의 해시를 고정한다. [overlay](overlay/)의 세 변경 조각만
별도로 관리하고 `scripts/materialize.py`가 빌드용 복사본을 만든다. 원본 해시가
달라지거나 출력 경로에 심볼릭 링크가 있으면 중단한다. 생성한 `jasmin/`, `include/`,
`test/`, `kat/`와 `build/`는 Git에 중복 저장하지 않는다.

전체 KeyGen/Sign/Verify 정확성, Hyperball 외부 재시도의 종료, 실제 SHAKE의
확률분포와 공식 Rényi 경계는 별도 과제다. Gaussian 거부율은 위 후속 증명에서 다룬다.
기반 코드의 MIT 라이선스와 저작권은 [LICENSE](LICENSE)에 유지한다.
