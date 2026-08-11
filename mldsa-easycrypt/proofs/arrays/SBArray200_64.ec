from Jasmin require import JByte_array.

require import BArray64 BArray200.

clone SubByteArray as SBArray200_64  with theory Asmall <= BArray64,
                                          theory Abig <= BArray200.
