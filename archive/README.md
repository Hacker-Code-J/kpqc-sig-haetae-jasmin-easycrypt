# HAETAE-1.2.0 이전 작업 보관

2026-09-17 재시작을 위해 과거 작업의 읽기 자료 39개만 `legacy/`에 남겼다.
기존 구현·증명·주차별 보고서·비교용 ML-DSA 전체는 아래 Git 태그로 복원한다.
이 자료는 이전 소스에 대한 기록이며 HAETAE-1.2.0 검증 결과가 아니다.

## 남긴 자료

`legacy/` 아래에서는 원래 경로와 파일 내용을 그대로 유지한다.

| 자료 | 용도 |
| --- | --- |
| [최신 post-freeze 경계](legacy/haetae-topdown-easycrypt/manifests/post-freeze-paper-artifacts.md) | 169개 대상의 성과, 조건, 남은 의무 |
| [동결 논문 경계](legacy/haetae-topdown-easycrypt/manifests/paper-artifacts.md) · [논문 PDF](legacy/haetae-topdown-easycrypt/latex/main.pdf) | 이전 82개 대상의 논문 기준점 |
| [주장 원장](legacy/haetae-topdown-easycrypt/CLAIM_LEDGER.md) · [정리 의존 관계](legacy/haetae-topdown-easycrypt/THEOREM_GRAPH.md) | 증명한 것과 미해결 항목의 구분 |
| [가정](legacy/haetae-ref-easycrypt/manifests/assumptions.md) · [입력 소스](legacy/haetae-topdown-easycrypt/manifests/source-roots.md) · [도구 버전](legacy/haetae-ref-easycrypt/manifests/toolchain.md) | 이전 증명 재현에 필요한 전제 |
| [보안 모델 대응 공백](legacy/haetae-security/PAPER_CORRESPONDENCE_GAPS.md) | 재사용 시 다시 검토할 보안 모델 경계 |
| [NTT 증명 안내](legacy/haetae-ntt-verify/easycrypt-ct/README.md) | 재사용 후보 NTT 코드·증명의 진입점 |
| [이론 안내서 PDF](legacy/haetae-topdown-easycrypt/theory-guide/main.pdf) · [대수학 안내서 PDF](legacy/haetae-topdown-easycrypt/algebraist-guide/main.pdf) | 각 안내서의 최신 로컬 수정 및 `.tex`·`.bib`·README 원본 |
| [post-freeze 검증 요약](legacy/haetae-topdown-easycrypt/logs/verify-post-freeze-summary.txt) | `RESULT PASS post-freeze-theories=169`로 끝나는 과거 실행 기록 |
| [진행 중 검증 요약](legacy/haetae-topdown-easycrypt/logs/verify-all-summary.txt) | 재시작 당시 미커밋 로그. 163개 compile 행이 있으나 최종 `RESULT`가 없어 완료 증거로 사용하지 않음 |

안내서와 원장 안의 소스 링크·상대경로는 **이전 전체 트리 기준**이다.
여기에 복사하지 않은 파일은 태그에서 찾는다. 원본 문서의 내용·링크·해시를
고쳐 쓰지 않았으며, 원래 빌드 스크립트와 외부 증명 파일이 필요한 재현 작업은
아래처럼 전체 트리를 복원한 뒤 수행한다. 이번 정리에서 과거 증명을 재실행하지 않았다.

```sh
# 현재 저장소 루트에서 보관 문서의 바이트 무결성 확인
sha256sum --check archive/SHA256SUMS
```

## 전체 이력 복구

| 보관 태그 (`archive/pre-haetae-1.2.0/` 아래) | 보존한 상태 |
| --- | --- |
| `main-20260917` | 기존 `main`, `4bde1207e2a290952d491d5b41c4bd773081e3c4` |
| `ntt-foundation-20260917` | NTT 브랜치, `5a7b487be5fd402e21f3919203af42f21c428e81` |
| `kg-rq-haetae-bridge-20260917` | 마지막 기존 개발 커밋, `ce8b083226596c7c116f1ae95ede95a877117190` |
| `worktree-20260917` | 위 개발 커밋에 기존 미커밋 20개 파일을 그대로 보존한 스냅샷 |

`worktree` 스냅샷에는 안내서의 수정 소스·PDF뿐 아니라 `.xdv`,
`.fdb_latexmk`, 진행 중 로그도 원래 경로로 포함된다. 새 배포본 도입 및
archive 재배치 이전의 완전한 추적 파일 트리다.

```sh
# 별도 디렉터리에서 이전 구조 그대로 열기
git worktree add --detach ../haetae-pre-1.2.0 \
  archive/pre-haetae-1.2.0/worktree-20260917

# 복사할 파일을 먼저 확인하기
git show archive/pre-haetae-1.2.0/worktree-20260917:haetae-ref-jasmin/jasmin/sampler.jinc
```

원래 프로젝트 간 상대경로와 pinned manifest가 연결되어 있으므로 증명 루트
하나만 이 디렉터리로 옮겨 실행하지 않는다. `worktree`에서 필요한 도구 버전과
검증 스크립트를 확인한 뒤 선택적으로 새 작업에 가져온다.

추적하지 않았던 로컬 파일과 빌드 산출물은 이 컴퓨터의
`.omx/restart-backup/haetae-1.2.0-20260917/legacy-tree/`로 옮겨 별도 보존했다.
그 로컬 백업은 Git에 들어가지 않는다. 영구 복구의 기준은 위 태그다.

## main 정비 범위

기존 `main` → NTT → bridge가 하나의 조상 관계이므로 이력을 유지한 채
`main`을 전진시켰다. 두 옛 로컬 작업 브랜치는 태그 보존 후 정리한다.
원격 게시 시에는 `main`과 위 보관 태그를 함께 게시해야 다른 clone에서도
태그 이름으로 복구할 수 있다. 이번 정리는 로컬 Git에 한정하며 원격 push,
원격 브랜치 삭제, GitHub 설정 변경은 포함하지 않는다.

중복 참조 구현·프로파일링·비교 자료·중간 산출물을 현재 트리에서 덜어냈지만
기존 이력을 유지하므로 `.git` 용량을 줄이는 이력 재작성은 하지 않았다.
