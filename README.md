# HAETAE — Jasmin / EasyCrypt

HAETAE의 Jasmin 구현과 EasyCrypt 기계검증을 제공하는 학위논문 연구 아티팩트다.
참조 구현과 대응하는 구현, 구성요소 명세·증명, 산술 검사를 추가한 Hyperball
보강안, 재현 테스트와 검증 근거를 함께 관리한다.

연구 결과의 출발점은 [논문–아티팩트 대응표](docs/research-map.md)다.
정리별 전제와 범위는 [증명 범위](haetae-easycrypt/CLAIMS.md),
실행 기록은 [검증 기록](haetae-easycrypt/VALIDATION.md)에서 확인할 수 있다.

## 연구 내용

- **구성요소 정확성:** 실제 Jasmin 추출물의 Gaussian 산술·버퍼, Hyperball,
  SHAKE, NTT 곱셈과 API 메모리 보조함수를 명세에 연결한다.
- **분포와 반복 비용:** 명시적 독립 균등 난수 모형에서 Gaussian 출력 분포,
  거부율·기대 시도 횟수와 Hyperball 한 시도의 확률 경계를 다룬다.
- **산술 보강:** 계수 변환과 제곱합 넘침을 검사하여, 보강안이 승인한 반환
  벡터의 실제 정수 제곱합이 모드 상한 이하임을 증명한다.

전체 KeyGen/Sign/Verify 합성의 정확성, 실제 SHAKE를 iid 난수로 대체하는
보안 논증, Hyperball 외부 재시도의 종료, 전체 서명 위조불가능성은 이 결과에
포함되지 않는다. 보강안은 일부 입력을 추가 거부하므로 기존 구현과 모든 입력에서
동등한 구현으로 주장하지 않는다. KAT 통과와 기계검증의 범위도 구분한다.

## 재현 시작

지원 대상은 Linux x86-64다. Jasmin 2026.09.0, EasyCrypt r2026.09와 그에 맞는
Why3·프로버를 사용한다. 설치·도구 확인·자원 안내는 [환경 안내](env/README.md)를
따른다. 도구 버전의 숫자는 구현 폴더 이름과 별개다.

```sh
git clone https://github.com/Hacker-Code-J/kpqc-sig-haetae-jasmin-easycrypt.git
cd kpqc-sig-haetae-jasmin-easycrypt
bash env/bootstrap.sh
source env/activate.sh
bash scripts/reproduce.sh quick
bash scripts/reproduce.sh full
```

`quick`은 빠른 실행·무결성·회귀 확인, `full`은 공개 대상의 전체 재현 절차다.
실제 단계와 출력 위치는 [재현 스크립트](scripts/reproduce.sh)와 환경 안내에
명시한다. 빠른 검사의 성공을 전체 증명 재검사 성공으로 해석하지 않는다.
개별 작업은 다음 명령으로 실행할 수 있다.

```sh
make -C haetae-jasmin -j2 test
make -C haetae-easycrypt verify
python3 haetae-hardened/scripts/materialize.py
python3 haetae-hardened/scripts/verify.py --group all
```

## 저장소 구조

| 경로 | 역할 |
| --- | --- |
| [HAETAE/](HAETAE/) | 원본 참조 배포본, 라이선스, 공식 KAT |
| [haetae-jasmin/](haetae-jasmin/) | 참조 구현에 대응하는 Jasmin 구현과 테스트 |
| [haetae-easycrypt/](haetae-easycrypt/) | 기존 Jasmin 구현의 추출물·명세·증명 |
| [haetae-hardened/](haetae-hardened/) | Hyperball 보강 코드, 별도 추출물·증명·테스트 |
| [docs/research-map.md](docs/research-map.md) | 논문 주장·구현·증명·재현 명령의 대응 |
| [docs/HAETAE.md](docs/HAETAE.md) | 참조 배포본의 출처와 식별 정보 |
| [archive/](archive/) | 이전 연구 기록; 현재 결과와 구분하여 보존 |

`haetae-easycrypt`와 `haetae-hardened`는 모두 EasyCrypt를 사용한다. 전자는
기존 구현의 검증 작업 공간이고, 후자는 동작을 변경한 구현과 그 증명이다.
과거 검증 기록은 당시 소스·도구의 증거로 보존하며 현재 소스의 PASS로 자동
승계하지 않는다. 상세 연구 경과는 [연구 기록](docs/research-notes.md)에 있다.

## 인용과 공개 기준

인용 정보는 [CITATION.cff](CITATION.cff)에 있다. 논문에는 사용한 커밋 또는
고정된 아티팩트 릴리스를 함께 명시한다. 공개 소스를 고정하고 재현 결과를
연결하는 절차는 [릴리스 안내](docs/release.md)를 따른다.

프로젝트 라이선스는 [MIT](LICENSE)다. 참조 구현과 포함된 외부 코드의 기존
고지는 유지하며, 출처별 안내는 [THIRD-PARTY](docs/THIRD-PARTY.md)에 정리한다.
