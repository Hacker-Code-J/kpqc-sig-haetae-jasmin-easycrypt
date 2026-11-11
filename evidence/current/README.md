# 공개 준비 검증 결과

실행별 원본 요약·로그와 파일 해시는 [summary.json](summary.json)에 있다.
검증 시점의 소스는 [source-snapshot.json](source-snapshot.json)으로 식별한다.
이는 미커밋 작업 트리의 스냅샷이며, GitHub에 발행한 릴리스나 DOI를 뜻하지 않는다.

| 검사 | 결과 | 근거 |
| --- | --- | --- |
| 기존 구현의 생성물·명세·증명 | 277/277 PASS | [요약](baseline-proofs/summary.json) |
| 보강 명세·증명과 원본 의존 증명 | 177/177 PASS | [요약](hardened-proofs/summary.json) |
| 캐시 없는 소스의 빠른 재현 | 20단계 PASS | [요약](clean-source-quick/summary.json) |
| 공개 소스로 새로 설치한 도구의 빠른 재현 | 20단계 PASS | [요약](bootstrapped-quick/summary.json) |
| 새 도구의 참조 KAT·수치 인증서·경계 사례·CT/SCT·재추출 비교 | 8단계 PASS | [요약](supporting-checks/summary.json) |

보강안의 177개에는 기존 구현의 의존 명세·증명 147개가 포함된다.
두 전체 증명 검사는 454회 주 대상 실행이며 중복 없는 파일은 307개다.
두 검증기 모두 `-no-eco`, `Proofs:check` 및 EOF 완료 검사를 사용했다.
각 검사 대상의 기록된 해시를 현재 소스와 다시 대조했다.

전체 증명 명령은 기존 지원 도구 환경에서 각각 실행했다. 빠른 실행 검사와
추가 검사는 빌드 캐시·Git 이력·개인 논문 폴더를 제외한 소스 내보내기에서
수행했다. 독립 설치는 같은 Linux 호스트의 별도 opam root/switch에서 이루어졌다.
이는 새로운 가상 머신이나 다른 운영체제에서의 실행을 뜻하지 않는다.

새 도구로 구성한 환경의 전체 증명 집합 재실행과 GitHub Actions의 원격 실행은
수행하지 않았다. 전체 재현 명령의 모든 단계를 한 번의 runner 호출로 실행했다는
주장도 하지 않는다. 단계별 실행 명령과 도구 해시는 각각의 로그를 확인한다.
빠른 검사에서는 검증기 회귀와 일부 실제 증명 검사를 실행하지만 전체 증명
검사를 대신하지 않는다.

최초 환경 설치와 최종 검토된 스크립트 재확인 로그는 [bootstrap/](bootstrap/)에
보존했다. 환경 실행 파일은 새로 빌드되었으므로 역사 기록의 실행 파일 해시와
다를 수 있다. 새 Jasmin 추출물은 저장된 프로그램과 바이트 단위로 일치했다.
새 환경의 빠른 검사 자원 기록은 [resources.txt](bootstrapped-quick/resources.txt)에
있다. 빠른 검사와 추가 검사에서는 실행 전후 소스 스냅샷의 불변 여부도 확인했다.
원본 JSON·로그 안의 호스트 경로는 실행 당시의 기록이다.

이 결과의 범위는 연구 구성요소와 명시한 실험이다. 전체 서명 API 정확성,
구체적 SHAKE의 iid 대체, Hyperball 외부 재시도의 종료 또는 전체 서명 보안성의
완료를 의미하지 않는다.

저장된 증거의 파일 무결성은 저장소 루트에서 확인할 수 있다.

```sh
(cd evidence/current && sha256sum --check SHA256SUMS)
```
