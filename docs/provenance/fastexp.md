# Fastexp 출처와 동일 바이트의 공개 라이선스 근거

대상은 [`haetae-easycrypt/theories/ntt/Fastexp.ec`](../../haetae-easycrypt/theories/ntt/Fastexp.ec)
한 파일이다. 2026-11-12에 Formosa의 공식 후속 저장소에서 이 파일과 **바이트가
동일한 파일** 및 명시적인 `CC0-1.0 OR Apache-2.0` 배포 고지를 확인했다.
그 후속 리비전의 고지와 두 라이선스 원문을 보존한다. 기존 검증 소스, TSV,
잠금 파일과 루트 MIT 라이선스는 변경하지 않는다.

## 식별과 적용 범위

- 로컬 파일 SHA-256: `a1f7a3562c743eab602cf98f6380339c63aa3824448380e570b1dcbbb3e450b3`
- Git blob: `f7c412959f8d359619e592b8152e9537fc227495`
- 동일 파일을 명시적 라이선스로 배포하는 리비전:
  [`formosa-crypto/formosa-libjade@589038bbae572525ff6a8281f6bc07fa5a31ff7b`](https://github.com/formosa-crypto/formosa-libjade/blob/589038bbae572525ff6a8281f6bc07fa5a31ff7b/proofs/mlkem/eclib/Fastexp.ec)
- 해당 리비전의 [LICENSE](https://github.com/formosa-crypto/formosa-libjade/blob/589038bbae572525ff6a8281f6bc07fa5a31ff7b/LICENSE)와
  [README의 License 절](https://github.com/formosa-crypto/formosa-libjade/blob/589038bbae572525ff6a8281f6bc07fa5a31ff7b/README.md#license)은
  CC0 1.0 또는 Apache 2.0 중 선택할 수 있음을 명시한다. README가 별도 조건을
  언급하는 대상은 `bench/third_party/` 서브모듈이며, 이 파일은
  `proofs/mlkem/eclib/`에 있다.

이 파일에 대한 공개 근거는 **후속의 명시적 라이선스 리비전과 동일한 바이트**다.
과거 리비전 `475b874...`에 당시 라이선스가 있었다거나 나중 고지가 과거에
소급 적용된다고 주장하지 않는다. 로컬 루트 MIT 고지를 이 외부 지원 파일의
독자적인 재라이선스 근거로 사용하지 않는다. 이 조사 결과를 다른 NTT 지원
파일이나 Formosa의 모든 과거 파일로 확대하지 않는다.

## 확인한 이력

| 단계 | 불변 커밋 | 확인한 사실 |
| --- | --- | --- |
| 파일 추가 | [`b94dc0d4f553e82a656d2382f56d2edbc9ce3282`](https://github.com/formosa-crypto/formosa-libjade/commit/b94dc0d4f553e82a656d2382f56d2edbc9ce3282) | 2022-04-21, commit author Manuel Barbosa. `proof/correctness/eclib/Fastexp.ec` 추가. |
| 경로 이동 | [`3ad502b30e3f8205043564760b1be51e8efda8c1`](https://github.com/formosa-crypto/formosa-libjade/commit/3ad502b30e3f8205043564760b1be51e8efda8c1) | 2022-04-28, commit author Manuel Barbosa. `proof/eclib/Fastexp.ec`로 바이트 변경 없는 이동. |
| 주석 추가 | [`875080867bc7c457f19a7602eb047ad1c9a8f093`](https://github.com/formosa-crypto/formosa-libjade/commit/875080867bc7c457f19a7602eb047ad1c9a8f093) | 2022-07-05, commit author Antoine Séré. 주석·빈 줄 6개를 추가해 현재 blob 형성. |
| 기존 감사 기준 | [`475b87434506280fdfa1a1ba5da0af3787e00579`](https://github.com/formosa-crypto/formosa-libjade/commit/475b87434506280fdfa1a1ba5da0af3787e00579) | 기존 Formosa 체크아웃의 동일 파일. 당시 트리에서 이 파일에 적용되는 라이선스는 확인하지 못했다. |
| 후속 배치 | [`94a8711044b668b67cb503f8b5af9826db3aa470`](https://github.com/formosa-crypto/formosa-libjade/commit/94a8711044b668b67cb503f8b5af9826db3aa470) | 2026-06-29, 후속 트리의 `proofs/mlkem/eclib/Fastexp.ec`에서도 같은 blob. |
| 명시적 라이선스 추가 | [`b301e356c3fc52fa6522be5445534d228e809548`](https://github.com/formosa-crypto/formosa-libjade/commit/b301e356c3fc52fa6522be5445534d228e809548) | 2026-11-09, commit author Pierre-Yves Strub. SPDX 표현과 두 원문을 추가하고 README·opam에 같은 조건을 기록. |
| 이번에 확인한 배포본 | [`589038bbae572525ff6a8281f6bc07fa5a31ff7b`](https://github.com/formosa-crypto/formosa-libjade/tree/589038bbae572525ff6a8281f6bc07fa5a31ff7b) | 현재 로컬 파일과 정확히 같은 blob 및 위 라이선스 고지가 함께 존재. |

GitHub의 [커밋 비교](https://github.com/formosa-crypto/formosa-libjade/compare/475b87434506280fdfa1a1ba5da0af3787e00579...589038bbae572525ff6a8281f6bc07fa5a31ff7b)도
기존 pin이 후속 리비전의 조상임을 확인한다. commit author는 이력상의 작성자
필드로 기록했으며, 그것만으로 최초 작성자나 모든 권리자를 특정하지 않는다.
2022년 파일 추가 이전의 더 이른 원출처는 이번 조사에서 확인하지 못했다.

로컬 [NTT 출처 TSV](../../haetae-easycrypt/manifests/ntt-support-origin.tsv)는 이전
연구 스냅샷의 경로와 해시를 계속 보존한다. 로컬 Git에서는 `bc20daa...`의 기존
경로와 `c5313fa...`의 현재 경로를 확인했다. 이 기록은 TSV를 대체하거나 수정하지
않고, 같은 바이트에 대해 확인한 외부 이력·후속 라이선스 근거를 덧붙인다.

## 보존한 고지

다음 파일은 위 후속 리비전에서 읽은 원문이며 Git blob과 SHA-256으로 확인했다.
각 값은 [기계 판독 기록](fastexp.json)에 있다.

- [업스트림 SPDX 고지](../../LICENSES/formosa-libjade/UPSTREAM-LICENSE.txt)
- [CC0 1.0 원문](../../LICENSES/formosa-libjade/CC0-1.0.txt)
- [Apache 2.0 원문](../../LICENSES/formosa-libjade/Apache-2.0.txt)
- [업스트림 기여자 목록](../../LICENSES/formosa-libjade/CONTRIBUTORS.md)

기여자 목록은 프로젝트 전체의 목록이며, 모든 기여자가 이 파일을 작성했다고
주장하지 않는다. 루트 라이선스와 이 파일의 외부 고지는 각각의 범위를 유지한다.

## 저장소 이동

기존 `formosa-crypto/formosa-mlkem` 주소의
[이동 안내](https://github.com/formosa-crypto/formosa-mlkem/blob/d1e64d5fee2157b47e5030c4f0bdc07bb36a7bde/README.md)는
공식 후속 저장소를 가리킨다. 과거 커밋은 후속 저장소에서 확인할 수 있다.
이 경로 변경은 기존 파일 pin이나 검증 결과의 변경을 뜻하지 않는다.
