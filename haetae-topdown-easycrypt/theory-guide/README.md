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
- Week 16 Sign pass에서 78번째 대상으로 컴파일한 actual 세 helper 직접 호출,
  accepted-branch control과 `STOP-SIGN-CHAL-MODE2` 판정;
- Week 16 Verify pass에서 추가한 actual 다섯 helper의 순차 호출, V-1/V-2/V-5/V-6
  machine-word 복원식, W64 norm gate와 tail/mismatch word expression, 그리고
  `STOP-VERIFY-MATRIX-CRT` 판정;
- 위 82개 대상과 논문 PDF, 주장 행렬, 재현 절차를 일치시킨 `PAPER-FROZEN`
  경계;
- paper-freeze 이후 닫힌 odd-root/full-NTT spectral action, 2-by-3/2-by-4
  수학적 row product, `Rq.poly`→`HAETAE_Algebra.poly` 표현 보존;
- 실제 mode-2 `avec`의 SHAKE128/LE16/rejection 의미를 논문 `a`에 연결하고,
  독립적인 논문 `qj`를 finalizer 스냅샷과 합성한 보조 증명;
- 기존 보안 모델의 synthetic `haetae_mode23_qj_vector`가 실제 확장 및 논문
  `qj`와 다름을 컴파일된 반례로 고정한 최신
  `STOP-KG-AVEC-QJ — OBL-KG-SECURITY-EXPANDVECA-SEMANTICS` 판정;
- 아직 남은 고정 입력 종료/losslessness, 보안 모델 ExpandVecA 의미 정렬,
  절차 수준 Verify matrix/CRT, 그리고 연기된 힌트 (h) 코덱;
- 생성/재전달(product/replay)로 동결된 저장 관찰 \(\mu\) 간선과 남은 서명
  접미부, 문맥(context), highbits/LSB 및 EUF-CMA 의무.

동결 논문 상태의 운영상 기준(source of truth)은 `../CLAIM_LEDGER.md`와
`../manifests/paper-artifacts.md`이며, 최종 근거는 명명된 EasyCrypt 선언이다.
paper-freeze 이후 보조 결과는 동결된 주장 행렬을 소급 변경하지 않고
`../POST_FREEZE_KG_RQ_HAETAE_REPORT.md`와
`../POST_FREEZE_KG_ACTUAL_AVEC_QJ_REPORT.md`에 별도로 기록한다. 동결
매니페스트는 `Mode2SignAcceptedCore.ec`와 `Mode2VerifyCoreSequence.ec`를 포함한
82개 작성 검증 대상(authored target)으로 유지된다.
Verify 수정 전 78/78 완료 로그는
`../logs/verify-all-before-week16-verify.log`에 보존되어 있고 해시
`cf8056712327dc8211cf93ae427ac5053e8a9d2366747f171392468ac3ff0d75`를 가진다.
77번째 KeyGen 경계는 `../WEEK16_KG_NTT_MUL_REPORT.md`, 78번째 Sign control
경계는 `../WEEK16_SIGN_REPORT.md`, 82번째 Verify partial boundary는
`../WEEK16_VERIFY_REPORT.md`에 기록되어 있다. paper-freeze 직전 82/82 로그는
`../logs/verify-all-before-paper-freeze.log`에 보존되어 있고 SHA-256은
`4cd64e5a656be82710bca1410c4d19403a3c661d6b91b0319a0ea8f7c91646da`이다.
기준 커밋 `e87bcc3`에 추적된 82개 aggregate 요약은
`../logs/verify-all-summary.txt`이며, paper-freeze audit를 포함한 terminal
`RESULT PASS`와 SHA-256
`08ef9639dc73d56dba42d02999d07897d29bc8e60aa100a648e9437fd64387ad`를
유지한다. 동결 논문 PDF의 SHA-256은
`be935948028829556951863b44ceb2e6c5b2037820991b3a43a4b461b036e53d`이다.

Week 15의 `actual_rans_encode_all_six_success`와
`signature_pack_unpack_hbz_zero_success_mode2`는 고정 all-6/all-zero 입력에서
종료한 실제 실행이 반드시 성공함을 보인다. 이는 Hoare 부분정확성이므로 실제
종료, losslessness, 확률 1 성공이나 비공허 실행을 증명하지 않는다. 동결 논문
판정은 `PAPER-FROZEN`이며 그 내부 Verify 중단점은
`STOP-VERIFY-MATRIX-CRT`다. Verify 쪽은 canonical decoded \((x,v,h,c)\) 부분
정리와 남은 blocker만 확보된 상태다.
`actual_m23_matrix_finalize_semantic_snapshot`는 실제 두 KeyGen 보조절차의
스냅샷 의미를 닫는다. 77번째 파일의 `output_row_from_mode2_ntt_words`와
`actual_m23_matrix_snapshot_rows_explicit`는 마지막 동결 시점 rewrite와 직접
two-call harness의 두 active row consequence를 컴파일한다. paper-freeze 이후에는
`rq_mul_coeff_foldr_to_bigi`, full-NTT spectral action, native Rq row product와
`RqHAETAEBridge.rq_poly_dot3_repr`가 닫혔다. 실제 `avec`도 nonce 515/516의
SHAKE128, little-endian 16-bit parsing과 `<64513` rejection을 거쳐 논문 `a`로
해석됨이 증명되었다. 그러나 기존 보안 객체는 첫 계수가 401인 synthetic
generator이고 논문 `qj[0][0]=64513` 및 all-zero seed의 실제 첫 계수 44985와
다르다. 따라서 최신 보조 전선은 `STOP-KG-AVEC-QJ`이며, full KG-1--KG-4나
`A s = q j (mod 2q)`를 주장하지 않는다. Verify에서도 순수 NTT 기반은 닫혔지만
실제 2-by-4 절차 정리 `verify_matrix_ntt_acc_mode2_cols4_correct`와
`verify_crt_freeze_mode2_word_exact`가 combined matrix theorem을 계속 막는다.

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
`../WEEK16_SIGN_REPORT.md`, `../WEEK16_VERIFY_REPORT.md`,
`../WEEK16_KG_NTT_MUL_REPORT.md`, `../manifests/paper-artifacts.md`, 두
`../POST_FREEZE_KG_*.md` 보고서와 보존 로그에서 확인한다.
Week 14 및 Week 13 기록은 각각 그 아래 full-HBZ와 rANS 핵심 경계의 역사적
교차검사다. `../logs/verify-all-summary.txt`는 terminal `RESULT PASS`와 해시를
함께 확인할 때만 현재 aggregate 증거로 쓴다. Verify 수정 전 78/78 완료 로그는
`../logs/verify-all-before-week16-verify.log`에 보존되고 해시
`cf8056712327dc8211cf93ae427ac5053e8a9d2366747f171392468ac3ff0d75`를 가진다.
paper-freeze 직전 82/82 `-no-eco` aggregate는
`../logs/verify-all-before-paper-freeze.log`에 보존되며 위의 `4cd64...` 해시를
가진다. 기준 커밋의 frozen-suite 요약은 `08ef96...` 해시를 유지한다. post-freeze의
세 `KgActualAvecQj*.ec` 대상은 동결된 82개 매니페스트 밖의 보조 증명이므로
각각 fresh compile했다는 근거와 deterministic trace는 최신 post-freeze 보고서에서
별도로 확인한다.
