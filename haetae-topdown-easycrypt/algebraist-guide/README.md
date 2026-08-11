# 대수학자를 위한 HAETAE-2 검증 안내서

이 폴더는 순수 대수학자와 대수기하학자가
`haetae-topdown-easycrypt`에서 진행 중인 형식 검증을 독립적으로 읽을 수 있도록
만든 한국어 LaTeX 안내서다. 기존 `../latex/`는 주차별 연구개발 기록이고,
`../theory-guide/`는 수학자·암호이론가를 위한 상세 증명 현황서다. 이 문서는 그
둘을 반복하지 않고 다음 세 층 사이의 번역에 집중한다.

수학 용어는 `환(ring)`, `몫환(quotient ring)`,
`가환도식(commutative diagram)`처럼 한국어 뒤에 영어 원어를 병기한다.

1. 몫환(quotient ring)과 자유 모듈(free module) 위에 기술된 HAETAE-2의
   수학적 대상(mathematical object);
2. 그 대상을 정준 바이트열(canonical byte string), 접두부(prefix),
   메모리 구간(memory region)으로 표현하는 사상(map);
3. 실제 Jasmin 절차와 EasyCrypt의 Hoare/pRHL 정리(theorem)를 유한 상태기계(finite
   state machine)의
   refinement로 읽는 방법.

현재 스냅샷은 2026년 8월 10일에 다시 감사한 Week 13 종료 기준선이다. 운영상
source of truth는 `../CLAIM_LEDGER.md`이고, 최종 증거는 `../easycrypt/` 아래의
명명된 EasyCrypt 정리(theorem)다. 안내서의 문장은 이 스냅샷에 고정되어 있으며,
“현재”라는 표현도 모두 이 날짜를 뜻한다.

여기서 67개는 최신 aggregate-verified 기준선의 authored target 수다. Week 11에
rANS encoder closure 관련 파일 일곱 개가 manifest에 추가되어 `-no-eco`로 fresh
compile되었고, Week 12에는 actual decoder semantic-refinement 파일 여덟 개가,
Week 13에는 actual core composition 파일 두 개가 추가되었다. encoder의 핵심 정리(theorem)
`actual_rans_encode_trace_closure`와
`actual_rans_encode_trace_refinement`는 실제 generated encoder가 반환하는 성공
접미부(suffix)를 actual symbol array의 순수 `trace_bytes`와 정확히 연결한다.
따라서 `OBL-RANS-ENCODE-REFINEMENT`는 성공 조건부
부분정확성(success-conditioned partial correctness)으로 `PROVED`다. decoder의
`actual_rans_decode_trace_refinement`는 exact-trace 입력 관계(input relation)
아래에서 `bad=0`, 정확한 byte 소비, 1024개 기호(symbol) 복원과 출력 tail
프레임(frame)을 증명한다. 따라서 `OBL-RANS-DECODE-REFINEMENT`도
부분정확성(partial correctness)으로 `PROVED`다.
`Mode2RansActualInverse.ec`는 실제 encoder, suffix copy, decoder를 순서대로 부르는
`Mode2RansActualHarness.run`과 control 정리(theorem)를 정의한다.
`Mode2RansCoreCompositionBridge.ec`는 encoder suffix·copy 결과를 decoder의 exact
read/state 전제로 운송하고, `Mode2RansCoreActualInverse.ec`의
`actual_rans_encode_copy_decode_inverse`가 이 harness의 의미론적 역함수(semantic
inverse)를 닫는다. 따라서 `OBL-RANS-CORE-INVERSE`도 성공 조건부
부분정확성(success-conditioned partial correctness)으로 `PROVED`다. 다만 concrete
all-6 입력의 실제 성공 증인(success witness), encoder/decoder 종료성(termination),
production full-HBZ wrapper와 full signature codec은 여전히 `PARTIAL` 또는
`BLOCKED`다.

## 빠른 읽기 순서

- 30분: 본문의 1절, 2절, 6절
- 반나절: 1--6절과 8절의 정리 인덱스(theorem index)
- 증명 참여 준비: 전 장과 `../CLAIM_LEDGER.md`, `../WEEK13_REPORT.md`,
  `../RANS_ENCODER_INVARIANT.md`, `../RANS_DECODER_INVARIANT.md`,
  `../RANS_CORE_COMPOSITION.md`,
  `../easycrypt/refinement/sign/Mode2RansCoreActualInverse.ec`

## 문서 구성

- `main.tex`: 문서 진입점
- `status.tex`: 날짜, 타깃 수, 현재 gate를 한곳에 모은 스냅샷
- `preamble.tex`: 한글 글꼴, 상태 색상, 정리 환경(theorem environment), 도식 스타일
- `sections/01-reading-contract.tex`: 독자, 범위, 대수기하학적 비유의 한계
- `sections/02-algebraic-object.tex`: 몫환(quotient ring)·모듈(module)과 HAETAE-2 데이터 흐름
- `sections/03-representation-and-logic.tex`: 표현 사상(representation map), 메모리 제한, Hoare/pRHL 사전
- `sections/04-proved-spine.tex`: 현재 실제로 닫힌 증명 사슬
- `sections/05-rans-frontier.tex`: HBZ/rANS의 순수 역함수(pure inverse function)와 실제 루프 사이의 간극
- `sections/06-boundaries.tex`: 미해결 의무, 가정 표면, 과장 금지선
- `sections/07-roadmap.tex`: 대수학자가 참여할 수 있는 다음 작업
- `sections/08-source-index.tex`: 정리명(theorem name), 소스 경로, 용어 사전, 재현 방법
- `references.bib`: 고정된 로컬 명세와 프로젝트 문서

## 빌드

저장소 루트에서 다음을 실행한다.

```sh
sh haetae-topdown-easycrypt/algebraist-guide/build.sh
```

필요한 도구는 XeLaTeX, `latexmk`, BibTeX, `rg`이며, 한글 글꼴로
`Noto Serif CJK KR`, `Noto Sans CJK KR`, `Noto Sans Mono CJK KR`를 사용한다.
성공하면 `main.pdf`가 생성된다. undefined reference/citation이나 LaTeX 오류가
남으면 스크립트가 실패한다.

전체 EasyCrypt 증명 상태는 별도로 다음 명령으로 검증한다.

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

이 안내서의 PDF 빌드 성공은 EasyCrypt 증명 성공을 대신하지 않는다.
반대로 `verify-all.sh`도 이 안내서를 자동으로 빌드하지 않는다. 문서와 증명
기준선을 함께 갱신할 때에는 위 두 명령을 각각 실행해야 한다.

## 상태를 갱신할 때

1. 먼저 `../CLAIM_LEDGER.md`와 실제 `.ec` 정리(theorem)를 갱신하고 검증한다.
2. `status.tex`의 날짜, 타깃 수, 현재 gate를 갱신한다.
3. 4--7절의 상태표와 8절의 정리 인덱스(theorem index)를 함께 갱신한다.
4. `build.sh`와 `../scripts/verify-all.sh`를 모두 실행한다.

`PROVED`는 표시된 전제 아래에서 명명된 정리(theorem)가 fresh-compile된다는 뜻이다.
부모 정리(parent theorem), 종료성(termination), 분포 동일성(distributional
equality), 전체 API 보안으로 자동 승격되지 않는다.
