# HAETAE provable-security machine-checking

This folder manages the EasyCrypt files that are part of the HAETAE
provable-security proof surface.

The goal of this folder is to keep the security proof verification path
separate from generated implementation-validation artifacts such as
`HAETAE_FIPS202_KAT_Empty_Generated.ec`.

## Scope

The managed proof surface is listed in:

```text
provable-security/proof-files.txt
```

The corresponding EasyCrypt source copies are stored in:

```text
provable-security/easycrypt/
```

The manifest is intentionally focused on the reduction, hop-game, ROM, scheme,
transcript, and algebra/distribution support files needed for the
provable-security proof. The original project-root files are left in place for
compatibility with the existing repository layout.

## Excluded from this gate

The generated FIPS202 KAT certificate file is not part of the HAETAE
provable-security gate:

```text
HAETAE_FIPS202_KAT_Empty_Generated.ec
```

It is useful as a separate implementation or certification artifact, but it
should not block the machine-checking workflow for the provable-security
theorem.

## Verification

From the `haetae-security` directory, run:

```sh
sh provable-security/verify-provable-security.sh
```

The script compiles each manifest entry with:

```sh
easycrypt compile provable-security/easycrypt/<file>.ec \
  -I provable-security/easycrypt \
  -I kyber-security
```

Logs are written under:

```text
provable-security/logs/
```
