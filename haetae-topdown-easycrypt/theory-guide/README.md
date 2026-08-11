# HAETAE-2 이론 안내서(Theory Guide)

이 폴더는 기존 `../latex/`의 주차별 연구개발 기록과 별도로, 수학자와
암호이론가가 현재 검증 범위와 남은 의무를 빠르게 이해하도록 구성한 한국어
LaTeX 문서다.

문서는 다음을 중심으로 읽는다.

- mode-2 KeyGen의 992바이트 패킹 키(packed-key) 접두부 부분정확성;
- 그 접두부에서 구성되는 Sign/Verify 키-메모리(key-memory) 관계;
- 실제 공용 KeyGen/Sign/Verify 복사 보조절차(copy helper)의 992/1408바이트 보존;
- 실제 원시(raw) KeyGen의 순차 외부 내보내기(export)와 정수/64비트 주소 바인딩;
- 실제 원시 Sign의 정확 추적(exact trace) 및 성공한 Verify의 꼬리 구간(tail)과
  해시 입력 바인딩;
- 실제 Sign의 1474바이트 출력 및 길이 쓰기가 VK/SK/pre/message를 보존하는
  프레임 조건(frame condition);
- 실제 생성 해시의 구간 국소(region-local) 동치와 Sign→Verify 순차 추적;
- 실제 생성된 원시/내부(raw/internal) \(\mu\) 절차의 64/32바이트 접두부 동치;
- 실제 도전값 \(\mu_{32}\) 접미부(challenge suffix) 흡수까지의 국소 무손실(zero loss) 합성;
- 실제 mode-2 서명의 1056바이트 접두부 코덱(prefix codec) 왕복(round trip);
- 실제 HBZ 준비/적용(prepare/apply) 잎 역함수와 꼬리 프레임;
- 실제 13기호 HBZ 표 인증서(table certificate) 및 순수 rANS 단계 역함수;
- 공통 rANS `xs/cuts/bytes` 추적(trace), 0/1/2바이트 정규화(normalization) 및 상태 범위;
- 실제 인코딩 접미부 복사와 인코더 결과로 분기하는 검증 결합 모듈(harness);
- Week 10의 배열/목록 접미부 연결, 실제 단어 단계, 내부 바이트/프레임 불변식,
  최종 직렬화 잎 정리 및 실제 성공 시 크기 범위;
- Week 11의 꼬리 인식 불변식(tail-aware invariant), 생성 단어 단계 연결
  (generated word-step bridge), 한 기호 외부 전이, 최종 직렬화 합성
  (serialization composition) 및 실제 인코더 전체 접미부 정제;
- Week 12의 디코더 커서(cursor), 실제 표 단어 단계, 0/1/2바이트 재생
  (replay), 외부/내부 반복 불변식 및 실제 디코더 정확 추적 정제;
- Week 13의 실제 인코더→복사→디코더 핵심 역함수(core inverse), 복사된
  추적의 점별 디코더 입력 운반, 디코더 상태 구성 및 W64 크기 무랩(no-wrap)
  연결;
- 아직 남은 실제 인코더 성공 증인(success witness), 인코더/디코더 종료 및
  성공 조건부(success-conditioned) 실제 전체 HBZ 래퍼 합성;
- 생성/재전달(product/replay)로 동결된 저장 관찰 \(\mu\) 간선과 남은 서명
  접미부, 문맥(context), highbits/LSB 및 EUF-CMA 의무.

상태 판정의 운영상 단일 기준(source of truth)은 `../CLAIM_LEDGER.md`이며, 최종 근거는
`../easycrypt/` 아래의 명명된 EasyCrypt 선언이다. `../WEEK13_REPORT.md`가
기록한 Week 13 완료 검증 스냅샷은 67개 작성 검증 대상(authored target)이며
종료 표식은
`RESULT PASS authored-targets=67 cache=-no-eco`다. 실제 인코더와 디코더의
개별 정제에 더해, `actual_rans_encode_copy_decode_inverse`가 같은 실제 결합
모듈(harness) 안에서 실패 분기를 보존하고 성공 분기의 1024기호 왕복을
성공 조건부 Hoare 부분정확성으로 증명한다. 운영 판정 `GO-CORE`는
`OBL-RANS-CORE-INVERSE` 관문 통과를 뜻한다. 다음 단일 관문은 이 핵심 역함수를
실제 `_encode_hb_z1_full`/`_decode_hb_z1_full` 래퍼와 prepare/apply 역함수에
합성하는 것이다.

## 용어 표기(Terminology)

설명용 기술 용어는 처음 등장할 때 한글(영어) 순으로 병기하고, 같은 문맥에서
반복할 때는 한글을 우선한다. EasyCrypt 정리명과 절차명, 주장 식별자, 파일명,
코드 조각 및 `rANS`, `HBZ`, `W32`, `W64`, `EUF-CMA` 같은 표준 약어는 검색과
원문 대조를 위해 번역하지 않는다. PDF의 전체 원칙과 예시는
1장 「한글(영어) 병기 원칙」에 정리했다.

## 빌드(Build)

저장소 루트에서:

```sh
sh haetae-topdown-easycrypt/theory-guide/build.sh
```

XeLaTeX, `latexmk`, Noto CJK 글꼴이 필요하다. 성공하면 `main.pdf`가 생성되며,
정의되지 않은 참조/인용(undefined reference/citation)이 있으면 빌드는 실패한다.

증명과 문서를 함께 검증하려면 별도로 다음을 실행한다.

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

새 안내서의 빌드 성공은 EasyCrypt 검증 성공을 대신하지 않는다. 완료된 Week 13
전체 증명 검증 결과는 `../WEEK13_REPORT.md`의 검증 절과
`../logs/week13-independent-verifier.md`에서 확인한다.
`../logs/verify-all-summary.txt`는 검증 중 덮어쓰이므로, 마지막 줄이
`RESULT PASS authored-targets=67 cache=-no-eco`일 때만 해당 파일을 완료 증거로
사용한다.
