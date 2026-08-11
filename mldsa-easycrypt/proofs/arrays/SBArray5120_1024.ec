from Jasmin require import JByte_array.

require import BArray1024 BArray5120.

clone SubByteArray as SBArray5120_1024  with theory Asmall <= BArray1024,
                                             theory Abig <= BArray5120.
