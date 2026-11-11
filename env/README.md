# 재현 환경

지원 대상은 Linux x86-64다. 검증 도구와 SMT 증명기를 다음 조합으로 고정한다.
기존 도구가 설치되어 있으면 먼저 `bash scripts/check-environment.sh`로 확인할 수 있다.
이 검사는 Why3 서버에 필요한 로컬 Unix 소켓 생성·대기 권한도 확인한다.
격리 환경이 이를 금지하면 `local_unix_socket: FAIL`과 원인을 출력하고 중단한다.

| 도구 | 기준 |
| --- | --- |
| Jasmin compiler / extractor | 2026.09.0, 공식 추출 소스 배포본 |
| EasyCrypt | r2026.09, commit `2aaa14acf7b2ce234b475f24f9e85ba0bdaeb024` |
| Why3 | 1.8.2 |
| 핵심 OCaml switch | 5.4.0, `opam-switch.export`에 패키지 버전·메타데이터 기록 |
| Alt-Ergo | 2.6.0 |
| Z3 | 4.12.6 |
| CVC4 | 1.8 |
| CVC5 | 1.2.1, 공식 Linux x86-64 static 배포본 |

## 설치

Ubuntu 24.04에서 필요한 시스템 패키지를 설치한다. 이 명령만 관리자 권한을 쓴다.

```sh
sudo apt-get update
sudo apt-get install -y opam build-essential cmake ninja-build git python3 \
  wget unzip bzip2 pkg-config libssl-dev libgmp-dev libpcre2-dev libppl-dev \
  libmpfr-dev zlib1g-dev autoconf automake libtool cvc4
bash env/bootstrap.sh
source env/activate.sh
bash scripts/check-environment.sh
```

`bootstrap.sh`는 `env/.opam-root/`, `env/_opam/`, `env/provers/`,
`env/config/`, `env/downloads/`에만 환경을 구성하며 셸 설정 파일과 기존 전역
opam switch를 변경하지 않는다. 새 셸마다 `source env/activate.sh`를 실행한다.
Alt-Ergo의 `cmdliner < 2` 조건 때문에 증명기는 별도 OCaml 5.2.1 switch에
설치한다. Alt-Ergo·Z3 버전은 고정하되 이 증명기 switch의 간접 의존성은
설치 시 opam이 해결한다. 핵심 compiler switch는 전체 export의 메타데이터를 사용한다.

이 export는 기존 설치 상태에서 개인 `file://` 소스 참조를 다음 공개 소스로
대체한 것이다. 실행 파일의 해시는 빌드 환경에 따라 달라질 수 있으므로 새 실행에서
별도로 기록한다. 환경 설치 성공만으로 증명 재현을 주장하지 않는다.

- [Jasmin 공식 배포](https://github.com/jasmin-lang/jasmin/releases/tag/v2026.09.0)의
  `jasmin-compiler-v2026.09.0.tar.bz2`:
  SHA-256 `11fec571efb9f7b3a47fea324b4e2a68289e0b73b2248d237eccf139b5218190`.
- [EasyCrypt 고정 소스](https://github.com/EasyCrypt/easycrypt/tree/2aaa14acf7b2ce234b475f24f9e85ba0bdaeb024).
- [CVC5 공식 배포](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.2.1)의
  `cvc5-Linux-x86_64-static.zip`:
  SHA-256 `6d44abc233980a14d72cc5809287d27c3335b1d6ee863381d0b5ffcbd0d8de56`.

## 빠른 확인과 전체 재현

저장소 루트에서 실행한다.

```sh
bash scripts/reproduce.sh quick
bash scripts/reproduce.sh full
```

`quick`은 환경·공개된 과거 증거의 무결성, 원본 해시, Jasmin의 API·샘플러·KAT,
EasyCrypt 검증기 회귀, NTT 대상 목록, 보강안 materialization·추출 provenance
회귀 및 보강 구현의 API·KAT를 검사한다. 전체 증명 집합을 재실행하는 명령은 아니다.

`full`은 위 검사에 C 참조 구현 KAT, 수치 인증서 재생성 비교, 구성한 Hyperball
경계 사례, CT/SCT 검사와 기존 구현·보강안의 전체 선택 증명을 추가한다.
전체 증명 명령 안에서 Jasmin 재추출 일치와 각 로컬 증명의 주 대상 실행을 검사한다.
추출물이 다르면 자동으로 덮어써서 통과시키지 않는다.

```sh
bash scripts/reproduce.sh full --jobs 2 --output /tmp/haetae-reproduction
```

결과 디렉터리는 새 경로여야 하며 저장소 밖 또는 루트 `build/` 아래에 둔다.
기본값은 `build/reproduction/<UTC 시각>-<모드>/`다. 다른 소스 경로를 출력 경로로
지정하면 파일을 쓰기 전에 거부한다.
`summary.json`에는 단계별 명령·상태·종료 코드·실행 시간·로그 해시가 기록된다.
실행 전 실제 소스 파일의 SHA-256 목록과 Git의 변경 상태도 기록한다.
소스 export의 `SOURCE-MANIFEST.json`이 있으면 실제 파일·목록과 먼저 대조하며,
검사 종료 시 소스 변경이 발견되면 성공으로 처리하지 않는다.
첫 실패에서 중단하고 0이 아닌 종료 코드를 반환한다. 프로젝트별 상세 proof 로그는
각 `logs/`에 생성되며, 기존 `manifests/verification-results.json` 및 보존된 과거
증거 파일은 갱신하지 않는다. CI는 새 실행 로그를 별도 artifact로 보관한다.

## 독립 재현과 자원

논문에 사용할 최종 커밋을 빈 디렉터리에 clone하고 위 설치·전체 재현을 수행한다.
기존 `build/`, `logs/`, `.eco` 캐시나 개인 논문 폴더를 복사하지 않는다.
시스템 패키지와 소스 다운로드에는 네트워크가 필요하고, 설치 후 검사 자체에는
외부 자료를 내려받지 않는다.

공개 bootstrap으로 별도 설치했던 환경에서 커밋 `88a543f`의 전체 runner가
28단계 모두 통과했다. 이번 실행의 전체 시간은 약 **1시간 35분 53초**,
GNU time 최대 RSS는 **3,536,252 KiB(약 3.37 GiB)**였다.
[실행 기록](../evidence/full-replay-20261111/README.md)에 도구·소스·로그와 자원
정보가 있다. 같은 Linux 호스트에서의 실행이며 다른 머신의 설치·실행 시간이나
메모리를 보장하지 않는다. `--jobs 2`는 빌드 동시성 기본값이며 EasyCrypt 검사는 순차 실행된다.
실행 후 `summary.json`의 실측 시간을 공개 기준으로 사용한다. 프로버 시간 제한은
기존 검증기의 기본값을 유지하며, 다른 `EC_TIMEOUT`, `EC_MAX_PROVERS`,
`WHY3_SERVER_SOCKET`을 사용했다면 함께 기록한다. Why3 서버를 시작할 수 없는
격리 환경에서는 일반 Linux 셸 또는 로컬 소켓 사용이 허용된 환경에서 실행한다.

설치 흐름은 [opam switch import](https://opam.ocaml.org/doc/man/opam-switch.html)와
[해당 EasyCrypt 릴리스의 설치 안내](https://github.com/EasyCrypt/easycrypt/blob/r2026.09/INSTALL.md)를 따른다.
