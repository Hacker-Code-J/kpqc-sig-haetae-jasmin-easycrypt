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
- Week 14의 실제 전체 HBZ 인코더/디코더, production SignaturePack/Unpack
  경계의 정확 동치와 성공 조건부(success-conditioned) 래퍼 역함수;
- Week 15의 실제 all-zero HBZ→all-6 기호 연결, 1020바이트 정규화 예산,
  실제 인코더 실패 배제와 production 고정 입력 왕복(round trip);
- Week 16의 실제 `_kp_m23_matrix`→`_keypair_finalize_m23` 스냅샷 합성,
  KG-2형 low/high 분해와 스냅샷 한정 mod-`2q` 등식;
- Week 16 KG-NTT-MUL 감사에서 77번째 대상으로 컴파일한 `output_row`의
  full-invNTT/pointwise 표현 rewrite, actual 두 row consequence와
  `STOP-KG-NTT` 판정;
- 아직 남은 고정 입력 종료/losslessness, odd-root 직교성/full-NTT convolution,
  `Rq.poly`→보안 모델 list 곱셈 adapter, 그리고 연기된 힌트 (h) 코덱;
- 생성/재전달(product/replay)로 동결된 저장 관찰 \(\mu\) 간선과 남은 서명
  접미부, 문맥(context), highbits/LSB 및 EUF-CMA 의무.

상태 판정의 운영상 단일 기준(source of truth)은 `../CLAIM_LEDGER.md`이며, 최종
근거는 `../easycrypt/` 아래의 명명된 EasyCrypt 선언이다. 현재 매니페스트는
`Mode2KeygenNttMulBridge.ec`를 포함한 77개 작성 검증 대상(authored target)이다.
마지막 보존 전체 완료 로그
`../logs/verify-all-week16-kg-first-task.log`는 그 직전 76대상 기준선의
`RESULT PASS authored-targets=76 cache=-no-eco`를 기록한다. 77번째 경계 대상과
stop 판정은 `../WEEK16_KG_NTT_MUL_REPORT.md`에 기록되어 있다. 77번째 대상은
개별 `-no-eco` fresh compile을 통과했지만 최종 77대상 전체 완료 로그는 아직
없다. 덮어쓰기 요약 로그는 terminal `RESULT PASS`가 남은 실행만 증거로 삼는다.

Week 15의 `actual_rans_encode_all_six_success`와
`signature_pack_unpack_hbz_zero_success_mode2`는 고정 all-6/all-zero 입력에서
종료한 실제 실행이 반드시 성공함을 보인다. 이는 Hoare 부분정확성이므로 실제
종료, losslessness, 확률 1 성공이나 비공허 실행을 증명하지 않는다. 현재 운영
판정은 Week 16의 `STOP-KG-NTT`다.
`actual_m23_matrix_finalize_semantic_snapshot`는 실제 두 KeyGen 보조절차의
스냅샷 의미를 닫는다. 77번째 파일의 `output_row_from_mode2_ntt_words`와
`actual_m23_matrix_snapshot_rows_explicit`는 마지막 sound rewrite와 직접
two-call harness의 두 active row consequence를 컴파일한다. 그러나 논문 식
`A s = q j (mod 2q)`로 승격할 odd-root
orthogonality/full-NTT convolution과 `Rq.poly`--security-list adapter가 없다.
KeyGen은 KG-2/finalization에서 동결되었고 다음 단일 목표는 actual accepted
Sign core다.

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

새 안내서의 빌드 성공은 EasyCrypt 검증 성공을 대신하지 않는다. 검증 판정은
`../WEEK16_KG_NTT_MUL_REPORT.md`, 이전 스냅샷 보고서
`../WEEK16_KG_REPORT.md`, Week 15/16 surface scan과 보존 로그에서 확인한다.
Week 14 및 Week 13 기록은 각각 그 아래 full-HBZ와 rANS 핵심 경계의 역사적
교차검사다. `../logs/verify-all-summary.txt`는 진행 중 실행이 덮어쓰므로, 현재
77대상 매니페스트에 대해서는 마지막 줄이
`RESULT PASS authored-targets=77 cache=-no-eco`일 때만 전체 완료 증거로
사용한다. 현재는 77번째 대상의 개별 컴파일만 성공했고, 전체 완료는 보존된
76대상 로그까지만 확인된다.
