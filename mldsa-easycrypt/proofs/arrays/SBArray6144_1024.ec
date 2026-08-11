from Jasmin require import JByte_array.

require import BArray1024 BArray6144.

clone SubByteArray as SBArray6144_1024  with theory Asmall <= BArray1024,
                                             theory Abig <= BArray6144.
