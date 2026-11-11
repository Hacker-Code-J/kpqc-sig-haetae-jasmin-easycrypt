# 코드와 증명 자료의 출처

이 목록은 저장소에 포함된 고지와 출처 기록을 찾기 위한 안내다. 원본 파일의
라이선스·저작권·개별 고지를 대체하지 않는다.

| 대상 | 출처와 고지 | 저장소의 근거 |
| --- | --- | --- |
| 직접 작성한 프로젝트 문서와 EasyCrypt 연구 코드 | Ji, Yonghyeon의 MIT 고지 | [루트 LICENSE](../LICENSE), [EasyCrypt LICENSE](../haetae-easycrypt/LICENSE) |
| HAETAE 참조 구현·공식 KAT | Team HAETAE 배포본; 기존 MIT 고지 보존 | [원본 LICENSE](../HAETAE/LICENSE), [배포 출처](HAETAE.md), [파일별 SHA-256](UPSTREAM-SHA256SUMS) |
| Jasmin 구현과 보강안에 포함된 참조 코드 | Team HAETAE 기반 코드의 기존 고지 보존 | [Jasmin LICENSE](../haetae-jasmin/LICENSE), [보강안 LICENSE](../haetae-hardened/LICENSE) |
| KAT 생성 코드 | NIST-developed software 고지가 파일 머리에 포함됨 | [PQCgenKAT_sign.c](../haetae-jasmin/kat/PQCgenKAT_sign.c), [kat_api.h](../haetae-jasmin/kat/kat_api.h) |
| 참조 SHAKE/Keccak 코드 | Ronny Van Keer의 SUPERCOP 구현 및 Gilles Van Assche·Daniel J. Bernstein·Peter Schwabe의 TweetFips202 기반이라는 원본 고지 | [fips202.c](../HAETAE/reference_implementation/src/fips202.c) |
| 이전 NTT·SHAKE 지원 이론 | 기존 연구 스냅샷의 파일·커밋·이식 해시와 변경 내역 | [NTT 출처](../haetae-easycrypt/manifests/ntt-support-origin.tsv), [SHAKE 출처](../haetae-easycrypt/manifests/shake-support-origin.tsv) |
| `theories/ntt/Fastexp.ec` 지원 이론 | 동일 바이트를 배포하는 공식 후속 Formosa 리비전의 `CC0-1.0 OR Apache-2.0` 고지; 기존 pin은 그대로 유지 | [파일별 출처·라이선스 근거](provenance/fastexp.md), [보존한 업스트림 고지](../LICENSES/formosa-libjade/UPSTREAM-LICENSE.txt) |
| 수학적 명세와 분포 정의의 참고문헌 | HAETAE 명세와 논문·학위논문에서 정의한 수식의 대응 | [명세 출처 목록](../haetae-easycrypt/manifests/specification-sources.json) |

Jasmin, EasyCrypt, Why3, SMT 프로버, OpenSSL은 재현에 사용하는 외부 도구다.
설치 방법과 필요한 버전은 [환경 안내](../env/README.md)를 따른다. 도구 설치물의
라이선스는 해당 배포물에서 확인하며, 저장소 라이선스를 도구 전체에 적용하지 않는다.

참고 PDF의 링크·해시·사용 위치를 기록한 것이 그 PDF 자체를 이 저장소에
재배포한다는 뜻은 아니다. 역사 파일의 경로나 버전 표기는 원래 자료를 식별하기
위해 보존한다.

## 이전 지원 이론의 추가 출처 확인

`haetae-easycrypt/theories/ntt/Fastexp.ec`는 Formosa ML-KEM의 고정 커밋
`475b87434506280fdfa1a1ba5da0af3787e00579`에 있는
[`proof/eclib/Fastexp.ec`](https://github.com/formosa-crypto/formosa-mlkem/blob/475b87434506280fdfa1a1ba5da0af3787e00579/proof/eclib/Fastexp.ec)와
바이트 동일하다. SHA-256은
`a1f7a3562c743eab602cf98f6380339c63aa3824448380e570b1dcbbb3e450b3`이다.
기존 출처 TSV는 이전 로컬 연구 스냅샷까지의 경로와 해시를 보존한다.

동일한 바이트만으로 원저자나 복사 방향을 확정할 수는 없다. 확인한 Formosa
고지에서는 이 지원 파일에 적용되는 이용 조건을 확정하지 못했으므로, 원출처와
적용 조건은 추가 확인 사항으로 남긴다. 별도 저장소인 `crypto-specs`의 CC0
고지를 Formosa의 `proof/eclib`에 자동으로 적용하지 않는다. 이 확인 메모는
원본 지원 이론, 역사적 출처 TSV 또는 증명 해시를 변경하지 않는다.
