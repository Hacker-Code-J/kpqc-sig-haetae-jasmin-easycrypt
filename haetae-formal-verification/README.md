# HAETAE formal verification goal

이 디렉터리는 HAETAE-2 Jasmin 구현의 KeyGen, Sign, Verify 핵심 계산에
대한 최종 검증 목표를 정확한 수식과 실제 프로시저 경계로 정리한다.

문서는 완료된 전체 HAETAE 검증을 주장하지 않는다. KeyGen과 Sign은 종료한
accepted execution의 기능적 정확성, Verify는 canonical object parsing 이후의
핵심 계산, 그리고 이 세 결과의 제한된 completeness 합성을 목표로 한다.

현재 실행 계획은 `GO-MINCORE-7D`이다. 일주일 동안 세 actual core 정리와
decoded-object 합성에 집중하며, `h` codec, full parser, termination, 분포와
public API 전체 정리는 명시적으로 보류한다. 세부 일정은
`../haetae-topdown-easycrypt/WEEK16_MINCORE_PLAN.md`에 있다.

## Build

XeLaTeX, `latexmk`, BibTeX 및 Noto CJK 글꼴이 필요하다.

```sh
./build.sh
```

빌드 결과는 `main.pdf`이다. 보조 파일은 다음 명령으로 정리할 수 있다.

```sh
latexmk -c
```

## Structure

- `main.tex`: 문서 진입점
- `preamble.tex`: 한글, 수학, 표 및 정리 환경
- `sections/00-rationale.tex`: 대상별 검증 당위성, 실패 모델 및 범위의 충분성
- `sections/01-methodology.tex`: 추출, 표현 관계, Hoare 정리, 합성 및 검증 절차
- `sections/01-scope.tex`: 고정 파라미터와 검증 경계
- `sections/02-keygen.tex`: KeyGen 키 방정식 목표
- `sections/03-sign.tex`: Sign challenge/response/hint 목표
- `sections/04-verify.tex`: Verify 재구성 및 승인 목표
- `sections/05-composition.tex`: 제한된 Sign--Verify completeness
- `sections/06-artifact-plan.tex`: 산출물, 검증 기준, 비주장 및 일정
