# HAETAE-1.2.0 Jasmin

HAETAE-1.2.0 참조 구현에 대응하는 x86-64 Jasmin 구현이다. mode 2, 3, 5의
KeyGen, 서명, 검증을 포함한다. 알고리즘 본체는 `jasmin/`에 있으며 생산
라이브러리는 Jasmin이 생성한 어셈블리만으로 빌드한다.

## 기준 소스와 변경

- 비교 기준: [공식 배포본](../HAETAE-1.2.0/reference_implementation/).
  [파일별 SHA-256](../docs/UPSTREAM-SHA256SUMS)으로 고정한다.
- 출발점: 보존 커밋 `6177f8db0a2887314dbff213e5ca04234eece58e`의
  `haetae-ref-jasmin/`. 이전 빌드 산출물이나 KAT 벡터를 가져오지 않았다.
- 샘플러: 83비트·166항 CDT, 올림 `smulh48`, 10차 `approx_exp`, 26바이트
  난수 입력, 큰 표본의 시프트 오버플로를 피하는 분리 반올림으로 갱신했다.
- Gaussian 스트림: 공통 함수와 서명 내부 경로 모두 49 SHAKE 블록
  (6664바이트)과 26바이트 소비·이월 규칙을 적용했다.
- API: 분리 서명과 메시지 결합 서명을 구분하고, 같은 버퍼를 사용하는
  결합 서명은 메시지를 뒤에서부터 복사한다.

MIT 라이선스는 [LICENSE](LICENSE)에 있다. KAT 드라이버의 NIST 고지는
해당 파일에 유지한다.

## 빌드와 테스트

Linux x86-64, GNU Make, C11 컴파일러, Jasmin Compiler **2026.03.0**이 필요하다.
KAT에는 참조 구현과 동일하게 OpenSSL 개발 파일과 `libcrypto`가 필요하다.
`JASMINC`, `CC`, `CFLAGS` 등은 Make 변수로 지정할 수 있다.

```sh
make -C haetae-1.2.0-jasmin -j2 all
make -C haetae-1.2.0-jasmin -j2 test
```

| 대상 | 확인 내용 |
| --- | --- |
| `all` | 세 모드의 공유 라이브러리와 기본 실행 테스트 빌드 |
| `sign-test` | 모드별 무작위 서명·검증 100회; 실패 시 비정상 종료 |
| `api-test` | 8개 API, 문맥 길이, 입력 변조, 버퍼 중첩, 실패 시 출력 |
| `sampler-test` | 실제 C 샘플러와 CDT 경계·올림·희귀 꼬리·refill 차등 비교 |
| `interop-test` | C/Jasmin 키·서명 바이트 비교와 양방향 서명·검증·open |
| `kat` | 모드별 100개 공식 KAT의 `.req`·`.rsp` 바이트 일치 |
| `check-reference` | 고정한 배포본과 KAT 해시 확인 |

라이브러리는 `build/mode{2,3,5}/lib/libhaetae-mode{2,3,5}-jazz.so`에 생성된다.
테스트 프로그램은 `build/bin/`, 생성한 KAT는 `build/kat/`에 둔다.
모든 생성물은 `build/` 아래에 있고 Git에서 제외한다.

## API와 난수 연결

[include/api.h](include/api.h)를 포함하고 `HAETAE_CONFIG_MODE`를
`HAETAE_MODE2`, `HAETAE_MODE3`, `HAETAE_MODE5` 중 하나로 지정한다.

| API | 의미 |
| --- | --- |
| `crypto_sign_keypair` | 난수를 사용하는 키 생성 |
| `crypto_sign_keypair_internal` | 입력 seed를 사용하는 키 생성 |
| `crypto_sign_signature` | 분리 서명 |
| `crypto_sign_signature_internal` | raw prefix와 입력 난수를 사용하는 분리 서명 |
| `crypto_sign` | 서명과 메시지를 결합한 출력 |
| `crypto_sign_verify` | 문맥을 포함하는 분리 서명 검증 |
| `crypto_sign_verify_internal` | raw prefix를 사용하는 검증 |
| `crypto_sign_open` | 결합된 서명을 검증하고 메시지 복원 |

호출 형태는 1.2.0 C API와 호환된다. Jasmin의 x86-64 인자 수 제한 때문에
긴 인자 목록은 헤더의 얇은 C inline 함수가 descriptor로 전달한다. 공유
라이브러리가 내보내는 descriptor 심볼은 C 참조 라이브러리의 바이너리 ABI와
구분한다. 메시지 처리와 서명·검증은 Jasmin에서 실행한다.

무작위 API는 애플리케이션이 제공하는 다음 Jasmin 난수 함수를 사용한다.

```c
uint8_t *__jasmin_syscall_randombytes__(uint8_t *out, uint64_t outlen);
```

테스트에서는 [test/randombytes.c](test/randombytes.c)가 운영체제 난수에 연결한다.
KAT에서는 [kat/jasmin_randombytes.c](kat/jasmin_randombytes.c)가 참조 드라이버의
결정적 DRBG에 연결한다. 참조 C 알고리즘은 차등·상호운용 테스트 실행 파일에만
링크한다.

## 컴파일러 검사 범위

`jasmin-ct`가 설치되어 있으면 다음으로 변경된 샘플러의 CT/SCT 검사를 실행한다.

```sh
make -C haetae-1.2.0-jasmin sampler-ct
```

대상은 CDT, 올림 곱셈, 지수 근사, 단일 Gaussian 시도, 고정 버퍼 소비와
Gaussian 스트림 모듈이다. 이 검사는 소스의 명시적인 declassification 계약을
전제로 한다. KAT·차등 테스트 및 이러한 제한된 컴파일러 검사는 전체 알고리즘의
보안 증명이나 HAETAE-1.2.0에 대한 EasyCrypt 증명을 대신하지 않는다.

현재 소스에서 추출한 별도의 [EasyCrypt 검증 프로젝트](../haetae-1.2.0-easycrypt/README.md)가
있다. 샘플러·NTT·API 보조함수의 증명과 전체 API의 미완료 의무를 구분하여 기록한다.
