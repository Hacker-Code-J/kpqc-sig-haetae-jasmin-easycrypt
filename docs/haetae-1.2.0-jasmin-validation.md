# HAETAE-1.2.0 Jasmin 검증 기록

검증일: 2026-09-17. 대상은 [haetae-1.2.0-jasmin](../haetae-1.2.0-jasmin/README.md)이다.
이전 구현의 보존 커밋 `6177f8db0a2887314dbff213e5ca04234eece58e`에서 시작하여
고정된 [HAETAE-1.2.0 참조 소스](HAETAE-1.2.0.md)에 맞춰 수정했다.

## 재현 명령과 결과

```sh
make -C haetae-1.2.0-jasmin -j2 all
make -C haetae-1.2.0-jasmin -j2 test
make -C haetae-1.2.0-jasmin sampler-ct
```

Jasmin Compiler 2026.03.0 및 Linux x86-64에서 모두 통과했다. 생성된 어셈블리를
이전 빌드에서 복사하지 않고 새 디렉터리의 소스로 컴파일했다.

| 검사 | 결과 |
| --- | --- |
| 기본 서명·검증 | mode 2·3·5 각각 100회 통과 |
| 공식 KAT | mode 2·3·5 각각 100개 응답; `.req`·`.rsp` 6개 파일 전체 일치 |
| API | 8개 API, 결정적 입력, 문맥 255/256, raw prefix 301, 빈 입력, 변조·길이 오류, 같은 버퍼의 서명·복원 및 실패 출력 통과 |
| C/Jasmin 상호운용 | 결정적 키·서명 바이트 일치, 무작위 서명의 양방향 검증, 결합 서명·open, SHAKE 블록 경계 메시지 통과 |
| 샘플러 차등 검사 | CDT 166개 임계점의 전후·동일 값과 borrow, signed ceiling, 지수 근사, 26바이트 입력, 최대 표본 166, dummy 출력·버퍼 경계 통과 |
| SHAKE 스트림 | 60개 결정적 사례; refill 4,355회, 반복 refill 사례 31개에서 C와 일치 |
| 회귀 검출 확인 | 임시 복사본에 옛 17바이트 stride, 옛 tail 반올림, 빠진 다항식 보정값을 각각 넣은 변이 3개 모두 실패 검출 |
| C 진단 | API·상호운용 테스트는 세 모드에서 `-Wall -Wextra -Werror` 통과; 샘플러 테스트도 엄격 진단 통과 |
| 링크 검사 | 세 생산 라이브러리의 유일한 필수 외부 심볼은 `__jasmin_syscall_randombytes__`; 참조 C 알고리즘에 연결되지 않음 |

샘플러 테스트는 배포본의 실제 `src/sampler.c`를 oracle로 사용한다. 다른
다항식을 복제한 upstream `test/test_sampler.c`는 사용하지 않는다. 상호운용
테스트는 참조 C 심볼을 `reference_haetae_` 접두사로 분리하여 두 구현을 실제로
호출한다. C 참조 코드는 테스트 실행 파일에만 연결한다.

## 메모리와 컴파일러 검사

가장 큰 파라미터 집합의 API 경계 검사를 다음처럼 실행하여 Valgrind 오류
0건, 종료 시 미해제 힙 0바이트를 확인했다.

```sh
cd haetae-1.2.0-jasmin
valgrind --error-exitcode=99 --leak-check=full --track-origins=yes \
  build/bin/haetae-mode5-api-test
```

`sampler-ct`는 CDT, 올림 곱셈, 지수 근사, 단일 Gaussian 시도, 고정 버퍼 소비와
Gaussian 스트림 모듈의 CT/SCT 검사를 수행했다. 별도로 `jasminc -checksafety`
검사에서 다음 세 slice의 `No Safety Violation`을 확인했다.

- `sample_gauss83_jazz`
- `smulh48_jazz`
- `sample_gauss_sigma76_jazz`

컴파일러 검사는 소스의 명시적인 declassification과 검사기 설정 범위에 따른다.
전체 KeyGen/Sign/Verify의 부채널 안전성 인증이나 새 EasyCrypt 증명을 의미하지
않는다. 위 기록은 기능 일치, 특정 메모리 경계, 제한된 컴파일러 검사에 대한 결과다.
