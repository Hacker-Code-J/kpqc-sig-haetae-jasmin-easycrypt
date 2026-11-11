# 공개 README 해시 연결 수정

일반 터미널에서 실행한 전체 재현은 환경·소켓 검사부터 NTT 대상 검사까지
10단계를 통과한 뒤 `Pinned baseline drift: haetae-easycrypt/README.md`로
중단됐다. [당시 요약](before-fix-full-summary.json)은 수정 전 기록이다.

공개 준비 중 개인 논문 폴더를 가리키던 링크 두 곳을 저장소 내부 근거로
바꿨지만, 해당 문서의 변경을 publication migration ledger에 등록하지 않은
것이 원인이었다. [검토한 차이](reviewed-readme.patch)는 그 두 줄뿐이다.

기존 문서 전용 승인 절차에 이 README의 정확한 이전·현재 SHA-256 쌍을
추가했다. 역사적 baseline/toolchain/layout lock, 구현·명세·증명 및 기존
검증 결과는 바꾸지 않았다. 미승인 문서 변경과 구현·증명 변경을 거부하는
검사는 유지한다.

실제 체크아웃 전체를 읽는 회귀 검사로 원래 실패를 재현한 뒤 수정했다.
이후 README에 추가 변경을 넣으면 계속 거부되는 것도 검사했다. 관련 테스트
묶음의 결과는 [검증 요약](summary.json)에 있다. EasyCrypt를 쓰는 회귀 검사는
준비된 환경을 활성화한 뒤 실행했다.

보강안의 출력 79개를 생성하고 재검사했다. 이전 출력과 비교하면 구현을
포함한 78개 파일은 바이트 동일하며, 나머지는 publication ledger 해시가
들어가는 생성 메타데이터다. 새 컴파일러 추출물 25개도 저장된 모델과 같다.
([출력 비교](materialization-preservation.json), [추출 검사](extraction-check.log))

이 결과는 문서 해시 연결 오류의 수정과 관련 검증이며, 전체 재현 완료를
뜻하지 않는다. 수정된 소스를 새로 내보내고 새 결과 디렉터리에서 `full`을
실행해야 한다. 수정 전 소스 스냅샷과 실패 결과를 덮어쓰지 않는다.

이 디렉터리에서 `sha256sum --check --quiet SHA256SUMS`로 기록을 확인할 수 있다.
