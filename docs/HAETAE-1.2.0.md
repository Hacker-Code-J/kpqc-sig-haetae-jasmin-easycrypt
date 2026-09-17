# HAETAE-1.2.0 작업 기준

## 출처와 범위

2026-09-17 재정비 시 작업 디렉터리에 있던 `HAETAE-1.2.0/`을 그대로 기준선으로
채택했다. `reference_implementation/CMakeLists.txt`의 프로젝트 버전은 `1.2.0`이다.
참조 구현, 테스트/벤치마크 소스, KAT, MIT 라이선스를 포함하며 최적화 구현은 없다.

[공식 HAETAE 배포 안내](https://kpqc.cryptolab.co.kr/haetae)는 구현 1.2.0의
hyperball sampler 변경과 대응 명세 260825 및 260904를 명시한다.

- [공식 1.2.0 배포 파일](https://drive.google.com/file/d/1pW6YS1wZ1gm8Neb8pY5EyYTkkdRIDmJ6/view)
- 공식 배포 ZIP의 공지 SHA-256:
  `e54f8f962eefadbb2929bca292797bc7ca18769fb9a273c10204f3887fd83e84`
- [대응 명세 260904](https://drive.google.com/file/d/1H2SFqZFG5BcWH--bJKssvXaSG0Sd3mUx/view)
- [UPSTREAM-SHA256SUMS](UPSTREAM-SHA256SUMS): 이 저장소에 제공된 파일 67개의
  SHA-256. ZIP 자체의 해시와는 별개의 파일별 무결성 기록이다.

공식 링크에서 ZIP을 내려받아 공지 해시와 일치함을 확인했고, 제공된 파일
67개 모두가 그 ZIP의 동일 경로 파일과 바이트 단위로 일치했다.
배포 ZIP과 macOS 메타데이터는 소스 트리에 중복 보관하지 않는다.

## 먼저 다시 확인할 부분

기존 `haetae-ref`와 새 참조 소스를 비교했을 때 다음 변화가 확인된다.
이전 경로는 [보관 태그](../archive/README.md)에서 열 수 있다.

| 항목 | 기존 구현 | 1.2.0의 기준 소스 |
| --- | --- | --- |
| Gaussian CDT | 16비트, 64항목 | `src/sampler.c`: 83비트, 166항목의 `sample_gauss83` |
| 한 번의 샘플링 입력 | 17바이트 | `src/sampler.c`: `GAUSS_RAND_BYTES = 26` |
| 지수함수 근사 | 이전 다항식 | `src/sampler.c`: 10차 `approx_exp`와 새 정수 계수 |
| 곱셈 반올림 | 이전 규칙 | `include/fixpoint.h`: `smulh48`의 올림 |
| 샘플 값 반올림 | 이전 결합 시프트 | `src/sampler.c`: 상·하위 limb를 나눈 계산 |

위 파일 경로는 모두 `HAETAE-1.2.0/reference_implementation/` 아래에 있다.
기존 Jasmin 샘플러의 17바이트 입력·stride·버퍼 크기와 이에 의존하는 증명은
새 구현으로 옮긴 뒤 다시 검증해야 한다. `params.h`의 바이트가 기존 참조본과
같다는 사실만으로 샘플러 분포나 전체 알고리즘의 동등성을 주장할 수 없다.
`mode2`/HAETAE-2는 파라미터 집합 이름이며 배포 버전 1.2.0과 구분한다.

## 재시작 순서

1. 아래 기준선 검증을 유지하면서 명세 260904와 함수별 대응표를 작성한다.
2. `smulh48`, `approx_exp`, `sample_gauss83`, 26바이트 파싱과 반올림을 우선
   이식한다. C/Jasmin 비교에는 실제 production 함수를 사용한다.
3. 난수 스트림 소비, rejection/refill, 고정소수점 범위를 새 샘플러에 맞춰
   연결한다. 이전 증명의 전제와 상수는 각각 재확인한다.
4. NTT·코덱 등 재사용 후보를 태그에서 필요한 만큼 가져와 현재 소스와 비교한다.
   이후 KeyGen/Sign/Verify 합성, 종료성·분포·보안 의무를 구분하여 진행한다.

구현 및 증명용 새 디렉터리는 실제 작업을 시작할 때 추가한다. 과거 소스의
일괄 복사는 하지 않는다.

## 재현과 검증 한계

```sh
# 저장소 루트에서
bash scripts/check-baseline.sh
```

2026-09-17 정리 전 기준선에서 `ref` mode 2·3·5 KAT의 `.req`·`.rsp` 6개가
모두 일치했고, 배포본의 `kat/SHA256SUMS` 검사도 통과했다. KAT를 생성해
덮어쓰는 `kat.sh update`는 이 검증에 사용하지 않는다.

KAT 일치는 제공된 C 구현의 재현성 검사다. 샘플러 분포의 정확성이나
Jasmin/EasyCrypt 검증을 대신하지 않는다. 특히 `test/test_sampler.c`는 기본
CMake 테스트 대상에 포함되지 않고 자체 근사함수를 포함하므로 production
샘플러의 검증 근거로 계산하지 않는다. `test/main.c`도 실패를 출력한 뒤 0으로
종료할 수 있어 실행 종료 코드만으로 성공을 판단하지 않는다.

정리 시점의 과거 증명 결과와 미해결 항목은 `archive`에 보존한다. 과거 전체
EasyCrypt 검증은 이번 구조 변경에서 다시 실행하지 않았다.
