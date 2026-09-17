# HAETAE-1.2.0 — Jasmin / EasyCrypt

HAETAE-1.2.0을 기준으로 Jasmin 구현과 EasyCrypt 검증을 새로 시작하는 저장소다.
현재 기준선은 제공된 C 참조 구현과 mode 2·3·5 KAT이며, 1.2.0에 대한 Jasmin
이식이나 형식 검증 완료를 주장하지 않는다.

| 경로 | 용도 |
| --- | --- |
| [HAETAE-1.2.0/](HAETAE-1.2.0/) | 수정하지 않은 참조 배포본, 라이선스, KAT |
| [docs/HAETAE-1.2.0.md](docs/HAETAE-1.2.0.md) | 배포 출처, 버전 차이, 재시작 순서 |
| [scripts/check-baseline.sh](scripts/check-baseline.sh) | 배포본 해시 확인과 참조 KAT 재현 |
| [archive/README.md](archive/README.md) | 과거 핵심 문서, 보관 기준, 전체 이력 복구 방법 |

## 기준선 확인

Linux에서 Bash, CMake 3.18 이상, C11 컴파일러, OpenSSL 개발 파일,
`make`, `diff`, `sha256sum`이 필요하다. 참조 구현이 이미 요구하는 도구들이다.

```sh
bash scripts/check-baseline.sh
```

배포본 SHA-256을 확인한 뒤 mode 2·3·5의 KAT를 생성하여 저장된 `.req`·`.rsp`
6개와 바이트 단위로 비교한다. 생성물은 무시되는
`HAETAE-1.2.0/reference_implementation/build/`에만 생성된다.
이 배포본에는 최적화 구현이 없으므로 검증 대상은 `ref`다.

## 작업 방식

- 통합 기준 브랜치는 `main`이다. 작업 브랜치는 짧게 유지하고 검증 후 통합한다.
- `HAETAE-1.2.0/`은 비교 기준으로 보존한다. 새 Jasmin/EasyCrypt 코드는 별도
  경로에서 시작하고, 검증한 함수와 가정을 함께 기록한다.
- 샘플러 변경의 영향을 먼저 확인한다. 과거 증명은 재사용 후보이며 1.2.0의
  검증 결과로 자동 승계하지 않는다.
- 커밋은 변경 이유를 첫 줄에 쓰고 `Tested:`, `Not-tested:`, `Directive:` 등
  Git-native Lore trailer로 검증 범위와 남은 의무를 기록한다.

과거 브랜치와 미커밋 문서 수정은 `archive/pre-haetae-1.2.0/*` 태그로 보존한다.
기존 Git 이력을 유지하므로 과거의 큰 파일도 이력에는 남아 있다.
