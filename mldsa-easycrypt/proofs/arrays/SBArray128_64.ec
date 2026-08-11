from Jasmin require import JByte_array.

require import BArray64 BArray128.

clone SubByteArray as SBArray128_64  with theory Asmall <= BArray64,
                                          theory Abig <= BArray128.
