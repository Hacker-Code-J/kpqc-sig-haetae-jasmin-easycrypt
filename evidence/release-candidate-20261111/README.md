# 공개 후보 점검과 전체 재현 시도

상태: **공개 후보 준비, 새 환경 전체 재현 미완료**.
이 디렉터리는 실패를 포함한 2026-11-11의 새 실행 기록이다. 기존
[`evidence/current`](../current/README.md)와 도구 이관 근거를 변경하지 않는다.

## 공개 소스 목록

[`executed-source-manifest.json`](executed-source-manifest.json)은 빌드 캐시,
Git 이력, 개인 논문 폴더 없이 내보낸 1,792개 파일(23,431,779바이트)을
식별한다. 기준 커밋은 `f836bf6f0e8e2107f1e5f839facf63a3e66fa356`이며,
실제로 실행한 대상은 그 위의 미커밋 작업 트리다. 기준 커밋만으로 이 실행
대상을 재구성할 수 있다는 뜻은 아니다.

[`source-inventory.json`](source-inventory.json)은 기존 네 구현·증명 디렉터리의
추적 파일 613개를 새 경로에 대응한다. 383개는 바이트 동일, 147개는 변경,
83개는 도구 이관으로 제거된 `Array*`/`WArray*` 생성 보조파일이다.
누락된 일반 구현·명세·증명 파일은 발견되지 않았다. 변경된 연구 내용 전부에
대한 독립 심사 완료를 뜻하지 않는다. 별도로 새 도구의 재추출 동일성 검사가
원본 58개와 보강안 25개 생성물에서 통과했다.

## 실제 실행 결과

새 도구는 공개 bootstrap으로 구성했던 별도 opam root/switch를 사용했다.
전체 실행 명령은 다음과 같다.

```sh
bash scripts/reproduce.sh full --jobs 2 --output /path/to/new-results
```

| 검사 | 새 실행 결과 | 근거 |
| --- | --- | --- |
| 전체 runner | **FAIL**, 28단계 중 8단계 PASS, 9번째 단계 실패 | [원본 요약](full-replay/summary.json) |
| 환경·증거·공개 도구 회귀·원본 해시·Jasmin API/샘플러/KAT | PASS | 위 요약의 1–8단계와 로그 |
| EasyCrypt 회귀 | Why3 서버 연결 실패 | [9번째 단계 로그](full-replay/09-easycrypt-gates.log) |
| 원본 재추출 비교 | 58개 생성물 PASS | [로그](fresh-extraction-check.log) |
| 보강안 구성과 재추출 비교 | 79개 구성 파일, 25개 생성물 PASS | [로그](fresh-hardened-extraction-check.log) |
| 사전 진단 추가 후 공개 도구 회귀 | 22개 PASS | [로그](public-tool-regressions.log) |
| 사전 진단 추가 후 환경 검사 | 예상된 FAIL, 로컬 소켓 권한 거부를 명시 | [결과](early-environment-check.json) |

전체 runner는 49.65초 후 종료 코드 1을 반환했고, 실행 전후 소스 해시는
같았다. 최대 RSS는 298,828 KiB였다. 이 값은 실패 지점까지의 자원 사용량이며
전체 증명 실행 비용이 아니다. [자원 기록](full-resources.txt)을 참고한다.

실행과 같은 격리 문맥의 AF_UNIX·AF_INET 진단은 모두 `EPERM`이었다.
Why3 서버의 로깅 진단도 `error binding socket`을 기록했다.
([소켓 진단](replay-context-bind-probe.json), [서버 진단](why3-server-logged.json))
일반적인 도구 버전 불일치나 수학적 증명 실패로 분류하지 않는다. 지원되는
외부 서버 진입점도 이 실행 문맥에서는 소켓을 만들 수 없어 사용할 수 없었다.

## 다음 실행과 기록의 경계

로컬 Unix 소켓이 허용되는 Linux 환경에서 같은 공개 소스와 고정 환경으로
`full`을 새 결과 디렉터리에 실행해야 한다. 검사 생략, 타임아웃 완화, 기존
PASS 복사로 이 실패를 대체하지 않는다. 이번 실행에서는 전체 원본·보강안
증명 단계에 도달하지 않았으며 새 전체 증명 PASS를 주장하지 않는다.

실행 후에는 `env/check.py`의 소켓 사전 진단, 해당 회귀 테스트, 문서의 공개
링크와 이 기록을 추가했다. 실행 대상 manifest는 그 이전 소스를 그대로
식별한다. 증명·명세·Jasmin 소스와 검증 기준은 이번 작업에서 변경하지 않았다.
최종 공개 후보의 파일 목록은 공개 후보를 다시 내보낼 때 생성되는
`SOURCE-MANIFEST.json`으로 식별한다.

이 폴더의 보존 파일은 다음과 같이 검증한다.

```sh
(cd evidence/release-candidate-20261111 && sha256sum --check SHA256SUMS)
```
