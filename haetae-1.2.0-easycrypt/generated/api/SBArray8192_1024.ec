from Jasmin require import JByte_array.

require import BArray1024 BArray8192.

clone SubByteArray as SBArray8192_1024  with theory Asmall <= BArray1024,
                                             theory Abig <= BArray8192.
