require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array1 Array2 Array3 Array4 Array5 Array6 Array7 Array8 Array16 Array24
Array25 Array26 Array32 Array48 Array61 Array64 Array66 Array128 Array136
Array168 Array256 Array272 Array320 Array416 Array640 Array680 Array768
Array848 Array1280 Array1536 Array1920 Array1952 Array2048 Array2496
Array3200 Array3309 Array4032 Array7680 WArray2 WArray8 WArray16 WArray32
WArray48 WArray61 WArray64 WArray66 WArray96 WArray128 WArray136 WArray160
WArray168 WArray192 WArray200 WArray208 WArray224 WArray256 WArray272
WArray320 WArray416 WArray512 WArray640 WArray680 WArray768 WArray800
WArray848 WArray1024 WArray1920 WArray1952 WArray2048 WArray2496 WArray3200
WArray3309 WArray4032 WArray5120 WArray6144 WArray30720.

abbrev commitment__ENCODING_SHUFFLES =
(W256.of_int
6809477063014005108496892811167092228318171255968858956394831878370493989120).

abbrev eRROR_VECTOR_SHUFFLE_TABLE =
((Array2048.of_list witness)
[(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7)]).

abbrev t1__mask =
(W256.of_int
27580025446916579586740047030762717305835781530194468456916412547466239).

abbrev t1__DECODING_TABLE =
((Array2.of_list witness)
[(W256.of_int
 (-1704488708535735317993730919615273811755981492442837930308886608702668544)
 );
(W256.of_int
161759680028012245712471816852122747571536270840244795705654356475904)]).

abbrev t1__SHUFFLE_TO_GROUP = (W128.of_int (-1152053784517354134044416)).

abbrev t1__ENCODING_SHIFTS_TABLE =
((Array3.of_list witness)
[(W256.of_int 138096238178506976811873579382829307350851889511329270071318);
(W256.of_int 8769009825346546976905862850151196547671258038272);
(W256.of_int 75325220824640169170112861481543258555010121551634147311628)]).

abbrev t0__DECODING_TABLE =
((Array3.of_list witness)
[(W256.of_int
 (-1683702690027913741012871262190298745403129414409667671300841849902661376)
 );
(W256.of_int
80879840039114529797782631482765660946599467588442375410801744805888);
(W256.of_int
220828923202046630884640982628521424684360592877637234731771588637630463)]).

abbrev t0__ENCODING_SHIFTS_TABLE =
((Array4.of_list witness)
[(W256.of_int 119264932972346934519345364012443492712099359123420733243411);
(W256.of_int 475368975159373001864691843072);
(W256.of_int 37662610412320084585056430740771629277505060775817073655814);
(W256.of_int 221360928884514619392)]).

abbrev matrix_A__DECODING_TABLE =
((Array3.of_list witness)
[(W256.of_int 31385508682779410369523405889615886801803926611390921441280);
(W256.of_int
(-432808243909779573675567928807470101786712732301848327860692622735061155584)
);
(W256.of_int
226156397384342666605459106258636701594091082888230722833791023177481060351)]
).

abbrev matrix_A__SHUFFLE_TABLE =
((Array256.of_list witness)
[(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 8); (W8.of_int 9);
(W8.of_int 10); (W8.of_int 11); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 8); (W8.of_int 9); (W8.of_int 10);
(W8.of_int 11); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 8); (W8.of_int 9); (W8.of_int 10); (W8.of_int 11);
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 8); (W8.of_int 9);
(W8.of_int 10); (W8.of_int 11); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 12); (W8.of_int 13);
(W8.of_int 14); (W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 12); (W8.of_int 13); (W8.of_int 14);
(W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 12); (W8.of_int 13); (W8.of_int 14); (W8.of_int 15);
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 12); (W8.of_int 13);
(W8.of_int 14); (W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 8); (W8.of_int 9);
(W8.of_int 10); (W8.of_int 11); (W8.of_int 12); (W8.of_int 13);
(W8.of_int 14); (W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 8); (W8.of_int 9); (W8.of_int 10);
(W8.of_int 11); (W8.of_int 12); (W8.of_int 13); (W8.of_int 14);
(W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 8); (W8.of_int 9); (W8.of_int 10); (W8.of_int 11); (W8.of_int 12);
(W8.of_int 13); (W8.of_int 14); (W8.of_int 15); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 8); (W8.of_int 9); (W8.of_int 10);
(W8.of_int 11); (W8.of_int 12); (W8.of_int 13); (W8.of_int 14);
(W8.of_int 15)]).

abbrev rOL8 =
((Array1.of_list witness)
[(W256.of_int
 13620818001941277694121380808605999856886653716761013959207994299728839901191
 )]
).

abbrev rOL56 =
((Array1.of_list witness)
[(W256.of_int
 10910488462195273559651782724632284871561478246514020268633800075540923875841
 )]
).

abbrev kECCAK_RHOTATES_RIGHT =
((Array6.of_list witness)
[(W256.of_int 144373339913893657577751063007562604548177214458152943091773);
(W256.of_int 232252764209307188274174373867837442080505530800860351692863);
(W256.of_int 156927543384667019098616994515559168111335794127330162507795);
(W256.of_int 351517697181654122777866749001917765472957616589092975280182);
(W256.of_int 276192476357013953622045746931053922384479139705868246843454);
(W256.of_int 313855086769334038206421612937983674734430261968315659321364)]).

abbrev kECCAK_RHOTATES_LEFT =
((Array6.of_list witness)
[(W256.of_int 257361171150853911329517531560668107745210100483895842570243);
(W256.of_int 169481746855440380633094220700393270212881784141188433969153);
(W256.of_int 244806967680080549808651600052671544182051520814718623154221);
(W256.of_int 50216813883093446129401845566312946820429698352955810381834);
(W256.of_int 125542034707733615285222847637176789908908175236180538818562);
(W256.of_int 87879424295413530700846981630247037558957052973733126340652)]).

abbrev kECCAK1600_RC =
((Array24.of_list witness)
[(W64.of_int 1); (W64.of_int 32898); (W64.of_int (-9223372036854742902));
(W64.of_int (-9223372034707259392)); (W64.of_int 32907);
(W64.of_int 2147483649); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854743031)); (W64.of_int 138); (W64.of_int 136);
(W64.of_int 2147516425); (W64.of_int 2147483658); (W64.of_int 2147516555);
(W64.of_int (-9223372036854775669)); (W64.of_int (-9223372036854742903));
(W64.of_int (-9223372036854743037)); (W64.of_int (-9223372036854743038));
(W64.of_int (-9223372036854775680)); (W64.of_int 32778);
(W64.of_int (-9223372034707292150)); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854742912)); (W64.of_int 2147483649);
(W64.of_int (-9223372034707259384))]).

abbrev zETAS_TO_INVERT_LAYER_6 =
((Array2.of_list witness) [(W32.of_int (-518909)); (W32.of_int (-2608894))]).

abbrev zETAS_TO_INVERT_LAYER_5 =
((Array4.of_list witness)
[(W32.of_int 466468); (W32.of_int (-876248)); (W32.of_int (-777960));
(W32.of_int 237124)]).

abbrev zETAS_TO_INVERT_LAYER_4 =
((Array8.of_list witness)
[(W32.of_int 2680103); (W32.of_int 3111497); (W32.of_int (-2884855));
(W32.of_int 3119733); (W32.of_int (-2091905)); (W32.of_int (-359251));
(W32.of_int 2353451); (W32.of_int 1826347)]).

abbrev zETAS_TO_INVERT_LAYER_3 =
((Array16.of_list witness)
[(W32.of_int 280005); (W32.of_int 4010497); (W32.of_int (-19422));
(W32.of_int 1757237); (W32.of_int (-3277672)); (W32.of_int (-1399561));
(W32.of_int (-3859737)); (W32.of_int (-2118186)); (W32.of_int (-2108549));
(W32.of_int 2619752); (W32.of_int (-1119584)); (W32.of_int (-549488));
(W32.of_int 3585928); (W32.of_int (-1079900)); (W32.of_int 1024112);
(W32.of_int 2725464)]).

abbrev zETAS_TO_INVERT_LAYER_2 =
((Array16.of_list witness)
[(W256.of_int
 55858097833101550257214085554898365818120118939289856544579935031533063981);
(W256.of_int
105163311027759753657778087208235454592057129092071682892877310237938875440);
(W256.of_int
25725989914184953801617746899476742653944181040072196426454101837991327827);
(W256.of_int
21889966941809614170064575509624246080299888430238795568055695825414134682);
(W256.of_int
(-43147210895140552674126020849390261598795394536363723224061988817370319988)
);
(W256.of_int
94555623449686201047046586089202287911895030785269406424979215626557937175);
(W256.of_int
94513323293355592920583638744342789667917531388272404646804202659466555225);
(W256.of_int
(-45812120743968864641291703575538650621127909064993469193858518144591140138)
);
(W256.of_int
63320826751879736535069744341302438400871249283798704129972914700106057053);
(W256.of_int
95437348505640655333834790623064550541058135367234548429171322106916072013);
(W256.of_int
96366226508326934740561615237334246202685117296625000557156943582056431169);
(W256.of_int
(-104095427540025280815714770235714915413038677656764623303505208897845490052)
);
(W256.of_int
(-68411269083022995552342786355098589395800322542083880897111870443293524305)
);
(W256.of_int
(-44799127707661490680986551545104751950660152152719002346056174221244420052)
);
(W256.of_int
82964517896806024708470005111380135907348798935390409998868367704828796613);
(W256.of_int
72954235777068957422335349253495230275540662222309750361511250266905736736)]).

abbrev zETAS_TO_INVERT_LAYER_1 =
((Array16.of_list witness)
[(W256.of_int
 (-81394801961692367886430385872069775591899888374899243279001081876171810855)
 );
(W256.of_int
34661567679679177301116532790068060848189603243687759106031639884244584450);
(W256.of_int
(-64955246559009626209334090610844950686859823444064428462419434932632520814)
);
(W256.of_int
5110203972054881556156591894762920528448975955081272796495122244267393014);
(W256.of_int
64416910343834614792393674441495836491133256368070832133925939380646307848);
(W256.of_int
(-100408034753660554592467491302376209402241585185804306979514679237786310208)
);
(W256.of_int
1194002118272767818204969697142475014804055004809772772326363503993317210);
(W256.of_int
(-90137400428898195608591888407911072567948167381482086222197180771257596536)
);
(W256.of_int
(-10298322189995975550492998599235942704890266878993213373882488288311628702)
);
(W256.of_int
(-18092847172484030768594150646838607120362146941117652454946646810846033417)
);
(W256.of_int
(-80007523985717796585815385341741418921177183815858461275034603165699132407)
);
(W256.of_int
91992999638536873929403675040794761538037322390893756773920815590270398111);
(W256.of_int
(-86006085160608795653219616202775328578590887095922183230672569182969532470)
);
(W256.of_int
(-33905098535969462031579012142083424424900777513339595321775290397735469834)
);
(W256.of_int
(-39157974545820129459247333378438079185440363582611062924321782937515733061)
);
(W256.of_int
(-105963212645560354748648894728962413671494752281642171317139502339957090279)
)]).

abbrev zETAS_TO_INVERT_LAYER_0 =
((Array16.of_list witness)
[(W256.of_int
 (-14947025766810884518519340178851830259972079680536628082551345248834016818)
 );
(W256.of_int
(-79236226866924585952449654367977996136871924539618190998681853009488910935)
);
(W256.of_int
(-11503350912960617613730640784158756079862038378229427709112689681143332901)
);
(W256.of_int
(-81929013263830893704991921825282108025075782622382010162513630324042812402)
);
(W256.of_int
(-85824995177798504282796294437560123626439291842320922633474527581536220099)
);
(W256.of_int
(-54286764273279474617153417324944689044923369866922433929488586482031684697)
);
(W256.of_int
(-14623371649451712728712467712169116528326753931430007783612848928714236385)
);
(W256.of_int
(-34499592299998942396114060243824569874827496206622141668637037974906472241)
);
(W256.of_int
(-35939172576451990257306214357269889304653686414943338569916213557288891026)
);
(W256.of_int
(-101558550446453650186530786043368056571637735915462539611172798861872728410)
);
(W256.of_int
76629361786750316726400779924715828393657363260547957195302525993867565638);
(W256.of_int
9228308866127115427653890041133811097211812064444699926619978848773806372);
(W256.of_int
(-17667554029197039999021031754983291937999381450166200406335605094401629758)
);
(W256.of_int
24282877894665662847114239626329772913956173036192043697149135726675756796);
(W256.of_int
7198224895570446916806461394142653175548603531300001347978374732042946014);
(W256.of_int
56391230786829500805896074122730759173243203946337935118236635448285439010)]).

abbrev lAYER_5_ZETAS =
((Array4.of_list witness)
[(W256.of_int
 6392850394989879782919009689269382774612906998598077359118130409487179332);
(W256.of_int
(-20973733154113172374116031522976669396413195272188229214344316118293536488)
);
(W256.of_int
(-23623572392751038233765597253728972386203994192070686609939037874369158872)
);
(W256.of_int
12575952404860491736722831142078028559353475404522730510421197583764889124)]).

abbrev lAYER_4_ZETAS =
((Array8.of_list witness)
[(W256.of_int
 49238217727174735462858186387578100159688428240787953942213019850271088171);
(W256.of_int
63448913458525191735085973044570427962987806332373120219353262977758521643);
(W256.of_int
(-9685360842428916145196834697753182983500981930324890315881936664396135251));
(W256.of_int
(-56397620285930186220742767687038759905129124854486734450534966836456319873)
);
(W256.of_int
84107835315332748371338501606473572188354819374915131634898543954979953269);
(W256.of_int
(-77775510000624713868157743535565931642824611623174616916724477422490879223)
);
(W256.of_int
83885793194530397492084942439958067066428266592234113411818227656112962121);
(W256.of_int
72255433959293710361838475334592620664244765969128822575549411552005776679)]).

abbrev lAYER_3_ZETAS =
((Array16.of_list witness)
[(W256.of_int
 73478364100347066145449536207869676010979875339599156186179113790095332952);
(W256.of_int
27610004907617431235323091930369958891020619642669127546773784053578440816);
(W256.of_int
(-29114019452687944652141730252662392625468968366251687480112978488363874908)
);
(W256.of_int
96676427654751394334623229099637232984438995494630684149338570296686720904);
(W256.of_int
(-14814140217741789410927691322378018811565773299786869881706381995571438192)
);
(W256.of_int
(-30183897976476251147078379349797082433450187480859935071749606949296084320)
);
(W256.of_int
70628374217605672732670001650962551502832747150821133068371149173069183336);
(W256.of_int
(-56846341638362717550793306634037796725107942789763916007716703659955858565)
);
(W256.of_int
(-57106154644454540695932518592234727621174745748323529001381711937296945706)
);
(W256.of_int
(-104058276733509297387884342293575725750886975620944943210190348485148730649)
);
(W256.of_int
(-37732062966262529937847409797042295828500025804886578957538547746756451081)
);
(W256.of_int
(-88365835373040579013342948867416487189184821000834832474730864937308128104)
);
(W256.of_int
47375015812574144245615171089146026461735045189417729391814688206912933941);
(W256.of_int
(-523589124344640168283556650424675203124767070476937215935262608098085854));
(W256.of_int
108122785253941937128917104982143485304890013997556525086078105349340869121);
(W256.of_int
7548919868293134767531912872774892140000535686570969834094701950491968965)]).

abbrev lAYER_2_ZETAS =
((Array16.of_list witness)
[(W256.of_int
 2582115852594215372922399554661124157277897753758022393249206975595104871);
(W256.of_int
95180393253896215529297919275801403125147833943906619600164777952522728653);
(W256.of_int
(-96844091563113441459207722112818379943157009722955851967939200150180289277)
);
(W256.of_int
105560026643059242874414333339279123590254343489504880656670121511773358036);
(W256.of_int
(-82058394089112118315595779323790756700487005185220852200797524175183604347)
);
(W256.of_int
(-77311583238268369291883430017183366157182291952749413423133918758353597802)
);
(W256.of_int
(-8100547337178139787008245328587635352700729757627470271676080386151676928));
(W256.of_int
(-14539445321086234152463082975167421569381635625639435689228564068424231268)
);
(W256.of_int
(-44317218660873969801110717389997338879307479034035967944316937582115679683)
);
(W256.of_int
(-103033744840025696354203701758616738032860190620728572595116874234736574946)
);
(W256.of_int
(-57711755926579748053954944473419501097706598159769197715058567402163436481)
);
(W256.of_int
99740910873226578859027498567763075504868159311739122747018415153785312348);
(W256.of_int
14325275504712524173736726246318565876195315536473979690242352211913630632);
(W256.of_int
104632712317280022276696336606463762131530400452447840796497601825375948662);
(W256.of_int
(-68933321490407250339359046639266418582417944507082254287320285389600881356)
);
(W256.of_int
(-75427945684089319846559526199054989292473894219667903397284946799304401580)
)]).

abbrev lAYER_1_ZETAS =
((Array16.of_list witness)
[(W256.of_int
 (-81992045660348812641476123197708666079241631123768297083540656699031157019)
 );
(W256.of_int
(-42737446665651130700293348505910636389708383368459145663957684787411823011)
);
(W256.of_int
(-26965365622709106780368661443443548512078695116176182616612116382728007819)
);
(W256.of_int
3421810351684802082964769067296309699936088410999557092647286114297533056);
(W256.of_int
73204208402624985713511618444513909716812773993549855077803124974272385266);
(W256.of_int
(-66781028067627493451451431699303436410367131290803476159769148694121498717)
);
(W256.of_int
(-35268139519884621783682773031740188428473545878656661145853861037123190142)
);
(W256.of_int
(-38564289560124577164223236705581139589637471190934819397139455616074765347)
);
(W256.of_int
83521699114705755838561325406274439130886830666761290636494297414977256425);
(W256.of_int
106724130180471185595712043181305186969900588105579027577994805152403467520);
(W256.of_int
(-87612466623198314199249342155859137881401108183911389095677359257120461878)
);
(W256.of_int
(-35502340576636688572867201419187530558567181874942573856296599846840404628)
);
(W256.of_int
(-49913672231130794101676053937559106172010661027002323394503420373148441492)
);
(W256.of_int
36162185271468838823349331853221926688304910074992295741345607920165534867);
(W256.of_int
(-38815340583547530020537411524095712066112549812346116746967645504362275291)
);
(W256.of_int
103525143788042270064916081275428900954501718048654818943189921863570681506)]
).

abbrev lAYER_0_ZETAS =
((Array16.of_list witness)
[(W256.of_int
 (-96043758579160644217776514638953766832040475090913850812646157387223274861)
 );
(W256.of_int
(-86093273615620618052689901656884593902421885036751304584651663901315558667)
);
(W256.of_int
(-14086545173911089561949528993457026072356098848467443862900796059865465250)
);
(W256.of_int
(-96943573748591673632705333890837508601762989505283144305719118595512467423)
);
(W256.of_int
5474055421981223595793975988818518111412432267915805729515223516017146137);
(W256.of_int
43027373937766165928586588799055057712463440178580726831465884900303527653);
(W256.of_int
(-28334095136827246491389516096410921694855453151494860059292548015584803560)
);
(W256.of_int
(-52912723625957039508985463083087738847792605820588336715244713961281836866)
);
(W256.of_int
91826414120696613313678319861910223306340101487465572345151919031776475475);
(W256.of_int
(-101827529838471838058920640338224688687792744157920897239160857356254332620)
);
(W256.of_int
(-32551035205553071989555012365732791000044387452985845181336240680081471912)
);
(W256.of_int
(-48503801831739795329241971286407911108857526471346587968315404362093466434)
);
(W256.of_int
12727197713517537082815509913119745890371516046578436962151070568165777724);
(W256.of_int
(-103361523849251602159785089487568870121220845713788474355019617747115344571)
);
(W256.of_int
(-95591532408285370970768713552277605216736587735721877751913636348105119900)
);
(W256.of_int
53293964247218654718527730774000289571803083760351434456930051142633097808)]).

abbrev tWO_POW_22_VECTOR =
(W256.of_int
113078212172144670016600318886917095060348232468446510094543828752187523072).

abbrev iNVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR =
(W256.of_int
1583315853253120773718772168429862829322770379248453373268938642773050925057).

abbrev polynomial__CONSTANTS_TABLE =
((Array5.of_list witness)
[(W256.of_int
 404399200101416122972727962327899080730729934460329449514903409786895);
(W256.of_int
27633945340263435069803077425739770516599878854789179050185066335437825);
(W256.of_int
14120973028821288748410904079750511260587920143459567849941203224302714368);
(W256.of_int
3423913227525323174502430081042878883520180111764122672559515536195711);
(W256.of_int
13803492696795003664135781114125621955608915096245911876775369720726016)]).

abbrev gamma1__DECODING_SHIFTS_TABLE =
((Array2.of_list witness)
[(W256.of_int
 (-425713140823427258726663558789254841410387362057345797737825556725963292416)
 );
(W256.of_int
107839786668602559184514066897402134367680229671084479353429526839296)]).

abbrev gamma1__ENCODING_SHIFTS_TABLE =
((Array2.of_list witness)
[(W256.of_int 75325220824640169170112861481543258555010121551634147311628);
(W256.of_int
(-392023588615790074933092468460461382420127193604147098349862656))]).

abbrev error_polynomial__SHIFTS =
(W256.of_int
107839786668602559184514066897402134367680229671084479353429526839296).

abbrev error_polynomial__DECODING_SHUFFLES =
(W256.of_int
(-6793906561703790865943291268746375741561545978554779831640812377080064)).

abbrev error_polynomial__ENCODING_SHUFFLES =
(W256.of_int
6809477063014005108496892811167092228318171255968858956394831878370493989120).

abbrev hALF_OF_BITS_IN_T0_VECTOR =
(W256.of_int
110427941574360029313086248913004975644871320769967295014202957765808128).

abbrev mODULUS_VECTOR =
(W256.of_int
225935595421087293402315996791205668696012104344015382954355885915737415681).

module M = {
  proc error_polynomial__encode (encoded:W8.t Array128.t,
                                 polynomial:W32.t Array256.t) : W8.t Array128.t = {
    var temp:W64.t;
    var shift:W256.t;
    var eta_0:W256.t;
    var encoding_shuffles:W256.t;
    var c0:W256.t;
    var c1:W256.t;
    var c2:W256.t;
    var c3:W256.t;
    var c4:W256.t;
    var c5:W256.t;
    var c6:W256.t;
    var c7:W256.t;
    var input_offset:int;
    var output_offset:int;
    temp <- (W64.of_int ((16 `<<` 8) + 1));
    shift <- (zeroextu256 (VMOV_64 temp));
    shift <- (VPBROADCAST_16u16 (truncateu16 shift));
    temp <- (W64.of_int 4);
    eta_0 <- (zeroextu256 (VMOV_64 temp));
    eta_0 <- (VPBROADCAST_8u32 (truncateu32 eta_0));
    encoding_shuffles <- error_polynomial__ENCODING_SHUFFLES;
    input_offset <- 0;
    output_offset <- 0;
    while ((output_offset < 128)) {
      c0 <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      input_offset);
      c0 <- (VPSUB_8u32 eta_0 c0);
      input_offset <- (input_offset + 32);
      c1 <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      input_offset);
      c1 <- (VPSUB_8u32 eta_0 c1);
      input_offset <- (input_offset + 32);
      c2 <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      input_offset);
      c2 <- (VPSUB_8u32 eta_0 c2);
      input_offset <- (input_offset + 32);
      c3 <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      input_offset);
      c3 <- (VPSUB_8u32 eta_0 c3);
      input_offset <- (input_offset + 32);
      c4 <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      input_offset);
      c4 <- (VPSUB_8u32 eta_0 c4);
      input_offset <- (input_offset + 32);
      c5 <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      input_offset);
      c5 <- (VPSUB_8u32 eta_0 c5);
      input_offset <- (input_offset + 32);
      c6 <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      input_offset);
      c6 <- (VPSUB_8u32 eta_0 c6);
      input_offset <- (input_offset + 32);
      c7 <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      input_offset);
      c7 <- (VPSUB_8u32 eta_0 c7);
      input_offset <- (input_offset + 32);
      c0 <- (VPACKUS_8u32 c0 c1);
      c1 <- (VPACKUS_8u32 c2 c3);
      c2 <- (VPACKUS_8u32 c4 c5);
      c3 <- (VPACKUS_8u32 c6 c7);
      c0 <- (VPACKUS_16u16 c0 c1);
      c1 <- (VPACKUS_16u16 c2 c3);
      c0 <- (VPMADDUBSW_256 c0 shift);
      c1 <- (VPMADDUBSW_256 c1 shift);
      c0 <- (VPACKUS_16u16 c0 c1);
      c0 <- (VPERMQ c0 (W8.of_int 216));
      c0 <- (VPSHUFB_256 c0 encoding_shuffles);
      encoded <-
      (Array128.init
      (WArray128.get8
      (WArray128.set256_direct (WArray128.init8 (fun i => encoded.[i]))
      output_offset c0)));
      output_offset <- (output_offset + 32);
    }
    return encoded;
  }
  proc error_polynomial__decode (decoded:W32.t Array256.t,
                                 encoded:W8.t Array128.t) : W32.t Array256.t = {
    var temp:W64.t;
    var mask:W256.t;
    var eta_0:W256.t;
    var decoding_shuffles:W256.t;
    var shifts:W256.t;
    var coefficients:W256.t;
    var bytes:W128.t;
    var input_offset:int;
    var output_offset:int;
    var byte_group:int;
    temp <- (W64.of_int ((1 `<<` 4) - 1));
    mask <- (zeroextu256 (VMOV_64 temp));
    mask <- (VPBROADCAST_8u32 (truncateu32 mask));
    temp <- (W64.of_int 4);
    eta_0 <- (zeroextu256 (VMOV_64 temp));
    eta_0 <- (VPBROADCAST_8u32 (truncateu32 eta_0));
    decoding_shuffles <- error_polynomial__DECODING_SHUFFLES;
    shifts <- error_polynomial__SHIFTS;
    coefficients <- (set0_256);
    input_offset <- 0;
    output_offset <- 0;
    while ((input_offset < 128)) {
      bytes <-
      (get128_direct (WArray128.init8 (fun i => encoded.[i])) input_offset);
      byte_group <- 0;
      while ((byte_group < 4)) {
        coefficients <- (VINSERTI128 coefficients bytes (W8.of_int 0));
        coefficients <- (VINSERTI128 coefficients bytes (W8.of_int 1));
        coefficients <- (VPSHUFB_256 coefficients decoding_shuffles);
        coefficients <- (VPSRLV_8u32 coefficients shifts);
        coefficients <- (VPAND_256 coefficients mask);
        coefficients <- (VPSUB_8u32 eta_0 coefficients);
        decoded <-
        (Array256.init
        (WArray1024.get32
        (WArray1024.set256_direct (WArray1024.init32 (fun i => decoded.[i]))
        output_offset coefficients)));
        output_offset <- (output_offset + 32);
        bytes <- (VPSRLDQ_128 bytes (W8.of_int 4));
        byte_group <- (byte_group + 1);
      }
      input_offset <- (input_offset + 16);
    }
    return decoded;
  }
  proc gamma1__coefficients_to_bytestream (gamma1:W256.t, coefficients:W256.t) : 
  W128.t * W128.t = {
    var bytestream_lower:W128.t;
    var bytestream_upper:W128.t;
    var shifts:W256.t;
    var bytestream:W256.t;
    coefficients <- (VPSUB_8u32 gamma1 coefficients);
    shifts <- gamma1__ENCODING_SHIFTS_TABLE.[0];
    bytestream <- (VPSLLV_8u32 coefficients shifts);
    bytestream <- (VPSRL_4u64 bytestream (W128.of_int 12));
    shifts <- gamma1__ENCODING_SHIFTS_TABLE.[1];
    bytestream <- (VPSHUFB_256 bytestream shifts);
    bytestream_lower <- (VEXTRACTI128 bytestream (W8.of_int 0));
    bytestream_upper <- (VEXTRACTI128 bytestream (W8.of_int 1));
    return (bytestream_lower, bytestream_upper);
  }
  proc gamma1____encode_polynomial (output:W8.t Array640.t,
                                    polynomial:W32.t Array256.t) : W8.t Array640.t = {
    var temp:W64.t;
    var gamma1:W256.t;
    var coefficients:W256.t;
    var lower:W128.t;
    var upper:W128.t;
    var final_output_block:W8.t Array16.t;
    var i:int;
    var output_offset:int;
    var input_offset:int;
    final_output_block <- witness;
    temp <- (W64.of_int (1 `<<` 19));
    gamma1 <- (zeroextu256 (VMOV_64 temp));
    gamma1 <- (VPBROADCAST_8u32 (truncateu32 gamma1));
    output_offset <- 0;
    input_offset <- 0;
    while ((input_offset < (((256 * 32) %/ 8) - 32))) {
      coefficients <-
      (get256_direct (WArray1024.init32 (fun i_0 => polynomial.[i_0]))
      input_offset);
      (lower, upper) <@ gamma1__coefficients_to_bytestream (gamma1,
      coefficients);
      output <-
      (Array640.init
      (WArray640.get8
      (WArray640.set128_direct (WArray640.init8 (fun i_0 => output.[i_0]))
      output_offset lower)));
      output_offset <- (output_offset + 10);
      output <-
      (Array640.init
      (WArray640.get8
      (WArray640.set128_direct (WArray640.init8 (fun i_0 => output.[i_0]))
      output_offset upper)));
      output_offset <- (output_offset + 10);
      input_offset <- (input_offset + 32);
    }
    coefficients <-
    (get256_direct (WArray1024.init32 (fun i_0 => polynomial.[i_0]))
    input_offset);
    (lower, upper) <@ gamma1__coefficients_to_bytestream (gamma1,
    coefficients);
    output <-
    (Array640.init
    (WArray640.get8
    (WArray640.set128_direct (WArray640.init8 (fun i_0 => output.[i_0]))
    output_offset lower)));
    output_offset <- (output_offset + 10);
    final_output_block <-
    (Array16.init
    (WArray16.get8
    (WArray16.set128_direct
    (WArray16.init8 (fun i_0 => final_output_block.[i_0])) 0 upper)));
    i <- 0;
    while ((i < 10)) {
      output.[(output_offset + i)] <- final_output_block.[i];
      i <- (i + 1);
    }
    return output;
  }
  proc gamma1____encode (encoded:W8.t Array3200.t, decoded:W32.t Array1280.t) : 
  W8.t Array3200.t = {
    var aux:W8.t Array640.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ gamma1____encode_polynomial ((Array640.init
                                          (fun i_0 => encoded.[((i *
                                                                ((20 * 256) %/
                                                                8)) +
                                                               i_0)])
                                          ),
      (Array256.init (fun i_0 => decoded.[((i * 256) + i_0)])));
      encoded <-
      (Array3200.init
      (fun i_0 => (if ((i * ((20 * 256) %/ 8)) <= i_0 < ((i *
                                                         ((20 * 256) %/ 8)) +
                                                        640)) then aux.[
                                                                   (i_0 -
                                                                   (i *
                                                                   ((20 *
                                                                    256) %/
                                                                   8)))] else 
                  encoded.[i_0]))
      );
      i <- (i + 1);
    }
    return encoded;
  }
  proc gamma1____decode_to_polynomial (polynomial:W32.t Array256.t,
                                       bytes:W8.t Array640.t) : W32.t Array256.t = {
    var temp:W64.t;
    var temp1:W128.t;
    var gamma1:W256.t;
    var gamma1_times_2_mask:W256.t;
    var coefficients:W256.t;
    var sixteen_bytes:W128.t;
    var shifts:W256.t;
    var input_offset:int;
    var output_offset:int;
    temp <- (W64.of_int (1 `<<` 19));
    temp1 <- (VMOV_64 temp);
    gamma1 <- (VPBROADCAST_8u32 (truncateu32 temp1));
    temp <- (W64.of_int (((1 `<<` 19) `<<` 1) - 1));
    temp1 <- (VMOV_64 temp);
    gamma1_times_2_mask <- (VPBROADCAST_8u32 (truncateu32 temp1));
    coefficients <- (set0_256);
    input_offset <- 0;
    output_offset <- 0;
    while ((output_offset < ((256 * 32) %/ 8))) {
      sixteen_bytes <-
      (get128_direct (WArray640.init8 (fun i => bytes.[i])) input_offset);
      input_offset <- (input_offset + 4);
      coefficients <- (VINSERTI128 coefficients sixteen_bytes (W8.of_int 0));
      sixteen_bytes <-
      (get128_direct (WArray640.init8 (fun i => bytes.[i])) input_offset);
      input_offset <- (input_offset + 16);
      coefficients <- (VINSERTI128 coefficients sixteen_bytes (W8.of_int 1));
      shifts <- gamma1__DECODING_SHIFTS_TABLE.[0];
      coefficients <- (VPSHUFB_256 coefficients shifts);
      shifts <- gamma1__DECODING_SHIFTS_TABLE.[1];
      coefficients <- (VPSRLV_8u32 coefficients shifts);
      coefficients <- (VPAND_256 coefficients gamma1_times_2_mask);
      coefficients <- (VPSUB_8u32 gamma1 coefficients);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      output_offset coefficients)));
      output_offset <- (output_offset + 32);
    }
    return polynomial;
  }
  proc gamma1____decode (decoded:W32.t Array1280.t, encoded:W8.t Array3200.t) : 
  W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ gamma1____decode_to_polynomial ((Array256.init
                                             (fun i_0 => decoded.[((i * 256) +
                                                                  i_0)])
                                             ),
      (Array640.init (fun i_0 => encoded.[((i * ((20 * 256) %/ 8)) + i_0)])));
      decoded <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  decoded.[i_0]))
      );
      i <- (i + 1);
    }
    return decoded;
  }
  proc polynomial__decompose (lows:W32.t Array256.t, highs:W32.t Array256.t,
                              polynomial:W32.t Array256.t) : W32.t Array256.t *
                                                             W32.t Array256.t = {
    var modulus:W256.t;
    var modulus_halved:W256.t;
    var mask:W256.t;
    var v:W256.t;
    var alpha:W256.t;
    var offs:W256.t;
    var shift:W256.t;
    var coefficients:W256.t;
    var upper:W256.t;
    var lower:W256.t;
    var comparisons:W256.t;
    var offset:int;
    modulus <- mODULUS_VECTOR;
    modulus_halved <- (VPSRL_8u32 modulus (W128.of_int 1));
    mask <- polynomial__CONSTANTS_TABLE.[0];
    v <- polynomial__CONSTANTS_TABLE.[1];
    alpha <- polynomial__CONSTANTS_TABLE.[2];
    offs <- polynomial__CONSTANTS_TABLE.[3];
    shift <- polynomial__CONSTANTS_TABLE.[4];
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      coefficients <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset);
      upper <- (VPADD_8u32 coefficients offs);
      upper <- (VPSRL_8u32 upper (W128.of_int 7));
      upper <- (VPMULHU_16u16 upper v);
      upper <- (VPMULHRS_16u16 upper shift);
      upper <- (VPAND_256 upper mask);
      lower <- (VPMULL_8u32 upper alpha);
      lower <- (VPSUB_8u32 coefficients lower);
      comparisons <- (VPCMPGT_8u32 lower modulus_halved);
      comparisons <- (VPAND_256 comparisons modulus);
      lower <- (VPSUB_8u32 lower comparisons);
      lows <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => lows.[i]))
      offset lower)));
      highs <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => highs.[i]))
      offset upper)));
      offset <- (offset + 32);
    }
    return (lows, highs);
  }
  proc polynomial__use_hints (commitment:W32.t Array256.t,
                              hint_polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var mask:W256.t;
    var lows:W32.t Array256.t;
    var highs:W32.t Array256.t;
    var low:W256.t;
    var hints:W256.t;
    var high:W256.t;
    var coefficients:W256.t;
    var offset:int;
    highs <- witness;
    lows <- witness;
    mask <- polynomial__CONSTANTS_TABLE.[0];
    (lows, highs) <@ polynomial__decompose (lows, highs, commitment);
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      low <- (get256_direct (WArray1024.init32 (fun i => lows.[i])) offset);
      hints <-
      (get256_direct (WArray1024.init32 (fun i => hint_polynomial.[i]))
      offset);
      hints <- (VPSIGN_8u32 hints low);
      high <-
      (get256_direct (WArray1024.init32 (fun i => highs.[i])) offset);
      coefficients <- (VPADD_8u32 high hints);
      coefficients <- (VPAND_256 coefficients mask);
      commitment <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => commitment.[i]))
      offset coefficients)));
      offset <- (offset + 32);
    }
    return commitment;
  }
  proc polynomial____make_hint (hints:W32.t Array256.t,
                                low_coefficients:W32.t Array256.t,
                                high_coefficients:W32.t Array256.t) : 
  W32.t Array256.t * int = {
    var temp:W64.t;
    var gamma2:W256.t;
    var minus_gamma2:W256.t;
    var low:W256.t;
    var high:W256.t;
    var abs_low:W256.t;
    var low_out_of_bounds:W256.t;
    var low_equals_minus_gamma2_and_high_is_nonzero:W256.t;
    var hint_block:W256.t;
    var num_hints:W64.t;
    var weight:int;
    var offset:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    temp <- (W64.of_int ((8380417 - 1) %/ 32));
    gamma2 <- (zeroextu256 (VMOV_64 temp));
    gamma2 <- (VPBROADCAST_8u32 (truncateu32 gamma2));
    temp <- (W64.of_int (- ((8380417 - 1) %/ 32)));
    minus_gamma2 <- (zeroextu256 (VMOV_64 temp));
    minus_gamma2 <- (VPBROADCAST_8u32 (truncateu32 minus_gamma2));
    weight <- 0;
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      low <-
      (get256_direct (WArray1024.init32 (fun i => low_coefficients.[i]))
      offset);
      high <-
      (get256_direct (WArray1024.init32 (fun i => high_coefficients.[i]))
      offset);
      abs_low <- (VPABS_8u32 low);
      low_out_of_bounds <- (VPCMPGT_8u32 abs_low gamma2);
      low_equals_minus_gamma2_and_high_is_nonzero <-
      (VPCMPEQ_8u32 low minus_gamma2);
      low_equals_minus_gamma2_and_high_is_nonzero <-
      (VPSIGN_8u32 low_equals_minus_gamma2_and_high_is_nonzero high);
      hint_block <-
      (VPOR_256 low_out_of_bounds low_equals_minus_gamma2_and_high_is_nonzero
      );
      hint_block <- hint_block;
      num_hints <- (zeroextu64 (MOVEMASK_8u32 hint_block));
      ( _0,  _1,  _2,  _3,  _4, num_hints) <- (POPCNT_64 num_hints);
      hint_block <- (VPSRL_8u32 hint_block (W128.of_int 31));
      hints <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => hints.[i]))
      offset hint_block)));
      offset <- (offset + 32);
      weight <- (weight + (W64.to_uint num_hints));
    }
    return (hints, weight);
  }
  proc polynomial____power2round (highbits:W32.t Array256.t,
                                  lowbits:W32.t Array256.t,
                                  polynomial:W32.t Array256.t) : W32.t Array256.t *
                                                                 W32.t Array256.t = {
    var half_t0_bits:W256.t;
    var temp:W64.t;
    var ones_vector:W256.t;
    var coefficients:W256.t;
    var high:W256.t;
    var low:W256.t;
    var offset:int;
    half_t0_bits <- hALF_OF_BITS_IN_T0_VECTOR;
    temp <- (W64.of_int 1);
    ones_vector <- (zeroextu256 (VMOV_64 temp));
    ones_vector <- (VPBROADCAST_8u32 (truncateu32 ones_vector));
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      coefficients <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset);
      high <- (VPADD_8u32 coefficients half_t0_bits);
      high <- (VPSUB_8u32 high ones_vector);
      high <- (VPSRA_8u32 high (W128.of_int 13));
      low <- (VPSLL_8u32 high (W128.of_int 13));
      low <- (VPSUB_8u32 coefficients low);
      highbits <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => highbits.[i]))
      offset high)));
      lowbits <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => lowbits.[i]))
      offset low)));
      offset <- (offset + 32);
    }
    return (highbits, lowbits);
  }
  proc montgomery_multiply_and_reduce (lhs:W256.t, rhs:W256.t) : W256.t = {
    var product_low:W256.t;
    var lhs_high:W256.t;
    var rhs_high:W256.t;
    var product_high:W256.t;
    var t_low:W256.t;
    var t_high:W256.t;
    lhs_high <- (VMOVSHDUP_256 lhs);
    rhs_high <- (VMOVSHDUP_256 rhs);
    product_low <- (VPMUL_256 lhs rhs);
    product_high <- (VPMUL_256 lhs_high rhs_high);
    t_low <-
    (VPMUL_256 product_low iNVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR);
    t_high <-
    (VPMUL_256 product_high iNVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR);
    t_low <- (VPMUL_256 t_low mODULUS_VECTOR);
    t_high <- (VPMUL_256 t_high mODULUS_VECTOR);
    product_low <- (VPSUB_4u64 product_low t_low);
    product_high <- (VPSUB_4u64 product_high t_high);
    product_low <- (VMOVSHDUP_256 product_low);
    product_low <- (VPBLEND_8u32 product_low product_high (W8.of_int 170));
    return product_low;
  }
  proc polynomial__pointwise_montgomery_multiply_and_reduce (product:W32.t Array256.t,
                                                             lhs:W32.t Array256.t,
                                                             rhs:W32.t Array256.t) : 
  W32.t Array256.t = {
    var lhs_coeffs:W256.t;
    var rhs_coeffs:W256.t;
    var product_coeffs:W256.t;
    var offset:int;
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      lhs_coeffs <-
      (get256_direct (WArray1024.init32 (fun i => lhs.[i])) offset);
      rhs_coeffs <-
      (get256_direct (WArray1024.init32 (fun i => rhs.[i])) offset);
      product_coeffs <@ montgomery_multiply_and_reduce (lhs_coeffs,
      rhs_coeffs);
      product <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => product.[i]))
      offset product_coeffs)));
      offset <- (offset + 32);
      lhs_coeffs <-
      (get256_direct (WArray1024.init32 (fun i => lhs.[i])) offset);
      rhs_coeffs <-
      (get256_direct (WArray1024.init32 (fun i => rhs.[i])) offset);
      product_coeffs <@ montgomery_multiply_and_reduce (lhs_coeffs,
      rhs_coeffs);
      product <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => product.[i]))
      offset product_coeffs)));
      offset <- (offset + 32);
    }
    return product;
  }
  proc polynomial__conditionally_add_modulus (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var modulus:W256.t;
    var zero:W256.t;
    var lhs:W256.t;
    var mask:W256.t;
    var rhs:W256.t;
    var offset:int;
    modulus <- mODULUS_VECTOR;
    zero <- (set0_256);
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      lhs <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset);
      mask <- (VPCMPGT_8u32 zero lhs);
      rhs <- (VPAND_256 modulus mask);
      lhs <- (VPADD_8u32 lhs rhs);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      offset lhs)));
      offset <- (offset + 32);
    }
    return polynomial;
  }
  proc polynomial__reduce32 (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var two_pow_22:W256.t;
    var modulus:W256.t;
    var a:W256.t;
    var t:W256.t;
    var offset:int;
    two_pow_22 <- tWO_POW_22_VECTOR;
    modulus <- mODULUS_VECTOR;
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      a <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset);
      t <- (VPADD_8u32 a two_pow_22);
      t <- (VPSRA_8u32 t (W128.of_int 23));
      t <- (VPMULL_8u32 t modulus);
      a <- (VPSUB_8u32 a t);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      offset a)));
      offset <- (offset + 32);
    }
    return polynomial;
  }
  proc polynomial__butterfly_2 (polynomial:W32.t Array256.t, start:W64.t,
                                zetas:W256.t) : W32.t Array256.t = {
    var lhs_start:W64.t;
    var lhs:W256.t;
    var rhs_start:W64.t;
    var rhs:W256.t;
    var summands:W256.t;
    var zeta_products:W256.t;
    var add_terms:W256.t;
    var sub_terms:W256.t;
    lhs_start <- start;
    lhs_start <- (lhs_start * (W64.of_int 32));
    lhs <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint lhs_start));
    lhs <- (VPSHUFD_256 lhs (W8.of_int 216));
    rhs_start <- lhs_start;
    rhs_start <- (rhs_start + (W64.of_int 32));
    rhs <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint rhs_start));
    rhs <- (VPSHUFD_256 rhs (W8.of_int 216));
    summands <- (VPUNPCKL_4u64 lhs rhs);
    zeta_products <- (VPUNPCKH_4u64 lhs rhs);
    zeta_products <@ montgomery_multiply_and_reduce (zeta_products, zetas);
    add_terms <- (VPADD_8u32 summands zeta_products);
    sub_terms <- (VPSUB_8u32 summands zeta_products);
    lhs <- (VPUNPCKL_4u64 add_terms sub_terms);
    lhs <- (VPSHUFD_256 lhs (W8.of_int 216));
    rhs <- (VPUNPCKH_4u64 add_terms sub_terms);
    rhs <- (VPSHUFD_256 rhs (W8.of_int 216));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint lhs_start) lhs)));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint rhs_start) rhs)));
    return polynomial;
  }
  proc polynomial__ntt_at_layer_0 (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- lAYER_0_ZETAS.[i];
      polynomial <@ polynomial__butterfly_2 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__butterfly_4 (polynomial:W32.t Array256.t, start:W64.t,
                                zetas:W256.t) : W32.t Array256.t = {
    var lhs_start:W64.t;
    var lhs:W256.t;
    var rhs_start:W64.t;
    var rhs:W256.t;
    var summands:W256.t;
    var zeta_products:W256.t;
    var add_terms:W256.t;
    var sub_terms:W256.t;
    lhs_start <- start;
    lhs_start <- (lhs_start * (W64.of_int 32));
    lhs <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint lhs_start));
    rhs_start <- lhs_start;
    rhs_start <- (rhs_start + (W64.of_int 32));
    rhs <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint rhs_start));
    summands <- (VPUNPCKL_4u64 lhs rhs);
    zeta_products <- (VPUNPCKH_4u64 lhs rhs);
    zeta_products <@ montgomery_multiply_and_reduce (zeta_products, zetas);
    add_terms <- (VPADD_8u32 summands zeta_products);
    sub_terms <- (VPSUB_8u32 summands zeta_products);
    lhs <- (VPUNPCKL_4u64 add_terms sub_terms);
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint lhs_start) lhs)));
    rhs <- (VPUNPCKH_4u64 add_terms sub_terms);
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint rhs_start) rhs)));
    return polynomial;
  }
  proc polynomial__ntt_at_layer_1 (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- lAYER_1_ZETAS.[i];
      polynomial <@ polynomial__butterfly_4 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__butterfly_8 (polynomial:W32.t Array256.t, start:W64.t,
                                zetas:W256.t) : W32.t Array256.t = {
    var lhs_start:W64.t;
    var lhs:W256.t;
    var lhs_truncated:W128.t;
    var rhs_start:W64.t;
    var rhs:W256.t;
    var rhs_truncated:W128.t;
    var summands:W256.t;
    var zeta_products:W256.t;
    var add_terms:W256.t;
    var sub_terms:W256.t;
    lhs_start <- start;
    lhs_start <- (lhs_start * (W64.of_int 32));
    lhs <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint lhs_start));
    lhs_truncated <- (truncateu128 lhs);
    rhs_start <- lhs_start;
    rhs_start <- (rhs_start + (W64.of_int 32));
    rhs <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint rhs_start));
    rhs_truncated <- (truncateu128 rhs);
    summands <- (set0_256);
    summands <- (VINSERTI128 summands lhs_truncated (W8.of_int 0));
    summands <- (VINSERTI128 summands rhs_truncated (W8.of_int 1));
    zeta_products <- (VPERM2I128 rhs lhs (W8.of_int 19));
    zeta_products <@ montgomery_multiply_and_reduce (zeta_products, zetas);
    add_terms <- (VPADD_8u32 summands zeta_products);
    sub_terms <- (VPSUB_8u32 summands zeta_products);
    lhs_truncated <- (truncateu128 add_terms);
    rhs_truncated <- (truncateu128 sub_terms);
    lhs <- (VINSERTI128 lhs lhs_truncated (W8.of_int 0));
    lhs <- (VINSERTI128 lhs rhs_truncated (W8.of_int 1));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint lhs_start) lhs)));
    rhs <- (VPERM2I128 sub_terms add_terms (W8.of_int 19));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint rhs_start) rhs)));
    return polynomial;
  }
  proc polynomial__ntt_at_layer_2 (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- lAYER_2_ZETAS.[i];
      polynomial <@ polynomial__butterfly_8 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_round (polynomial:W32.t Array256.t, step:int,
                              step_by:int, start:int, zetas:W256.t) : 
  W32.t Array256.t = {
    var coeffs_i:W256.t;
    var coeffs_i_plus_step:W256.t;
    var product:W256.t;
    var offset:int;
    var i:int;
    var bound:int;
    var index:int;
    var index_plus_step:int;
    offset <- start;
    offset <- (offset * step);
    offset <- (offset * 2);
    offset <- (offset `|>>` 3);
    i <- offset;
    bound <- offset;
    bound <- (bound + step_by);
    while ((i < bound)) {
      index <- i;
      index <- (index * 32);
      coeffs_i <-
      (get256_direct (WArray1024.init32 (fun i_0 => polynomial.[i_0])) index);
      index_plus_step <- i;
      index_plus_step <- (index_plus_step + step_by);
      index_plus_step <- (index_plus_step * 32);
      coeffs_i_plus_step <-
      (get256_direct (WArray1024.init32 (fun i_0 => polynomial.[i_0]))
      index_plus_step);
      product <@ montgomery_multiply_and_reduce (coeffs_i_plus_step, zetas);
      coeffs_i_plus_step <- (VPSUB_8u32 coeffs_i product);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct
      (WArray1024.init32 (fun i_0 => polynomial.[i_0])) index_plus_step
      coeffs_i_plus_step)));
      coeffs_i <- (VPADD_8u32 coeffs_i product);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct
      (WArray1024.init32 (fun i_0 => polynomial.[i_0])) index coeffs_i)));
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_at_layer_3 (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var i:int;
    var zetas:W256.t;
    var step:int;
    var step_by:int;
    var start:int;
    step <- (1 `<<` 3);
    step_by <- ((1 `<<` 3) %/ 8);
    i <- 0;
    while ((i < 16)) {
      start <- i;
      zetas <- lAYER_3_ZETAS.[i];
      polynomial <@ polynomial__ntt_round (polynomial, step, step_by, 
      start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_at_layer_4 (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var i:int;
    var zetas:W256.t;
    var step:int;
    var step_by:int;
    var start:int;
    step <- (1 `<<` 4);
    step_by <- ((1 `<<` 4) %/ 8);
    i <- 0;
    while ((i < 8)) {
      start <- i;
      zetas <- lAYER_4_ZETAS.[i];
      polynomial <@ polynomial__ntt_round (polynomial, step, step_by, 
      start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_at_layer_5 (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var i:int;
    var zetas:W256.t;
    var step:int;
    var step_by:int;
    var start:int;
    step <- (1 `<<` 5);
    step_by <- ((1 `<<` 5) %/ 8);
    i <- 0;
    while ((i < 4)) {
      start <- i;
      zetas <- lAYER_5_ZETAS.[i];
      polynomial <@ polynomial__ntt_round (polynomial, step, step_by, 
      start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__multiply (polynomial:W32.t Array256.t, start:W64.t,
                             step_by:W64.t, zeta_0:W32.t) : W32.t Array256.t = {
    var index_i_plus_step_by:W64.t;
    var coeffs_i_plus_step_by:W256.t;
    var constants:W256.t;
    var prod02:W256.t;
    var prod13:W256.t;
    var c02:W256.t;
    var c13:W256.t;
    var res02:W256.t;
    var res13:W256.t;
    var t:W256.t;
    var index_i:W64.t;
    var coeffs_i:W256.t;
    index_i_plus_step_by <- start;
    index_i_plus_step_by <- (index_i_plus_step_by + step_by);
    index_i_plus_step_by <- (index_i_plus_step_by * (W64.of_int 32));
    coeffs_i_plus_step_by <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint index_i_plus_step_by));
    constants <- (zeroextu256 (VMOV_32 zeta_0));
    constants <- (VPBROADCAST_8u32 (truncateu32 constants));
    prod02 <- (VPMUL_256 coeffs_i_plus_step_by constants);
    coeffs_i_plus_step_by <-
    (VPSHUFD_256 coeffs_i_plus_step_by (W8.of_int 245));
    constants <- (VPSHUFD_256 constants (W8.of_int 245));
    prod13 <- (VPMUL_256 coeffs_i_plus_step_by constants);
    constants <- iNVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR;
    c02 <- (VPMUL_256 prod02 constants);
    c13 <- (VPMUL_256 prod13 constants);
    constants <- mODULUS_VECTOR;
    c02 <- (VPMUL_256 c02 constants);
    c13 <- (VPMUL_256 c13 constants);
    res02 <- (VPSUB_8u32 prod02 c02);
    res13 <- (VPSUB_8u32 prod13 c13);
    res02 <- (VPSHUFD_256 res02 (W8.of_int 245));
    t <-
    (VPBLEND_8u32 res02 res13
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    index_i <- start;
    index_i <- (index_i * (W64.of_int 32));
    coeffs_i <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint index_i));
    coeffs_i_plus_step_by <- (VPSUB_8u32 coeffs_i t);
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint index_i_plus_step_by) coeffs_i_plus_step_by)));
    coeffs_i <- (VPADD_8u32 coeffs_i t);
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    (W64.to_uint index_i) coeffs_i)));
    return polynomial;
  }
  proc polynomial____layer (polynomial:W32.t Array256.t, _start:int,
                            _step_by:int, _zeta:int) : W32.t Array256.t = {
    var step_by:W64.t;
    var zeta_0:W64.t;
    var i:int;
    var start:W64.t;
    step_by <- (W64.of_int _step_by);
    zeta_0 <- (W64.of_int _zeta);
    i <- 0;
    while ((i < 4)) {
      start <- (W64.of_int (_start + i));
      polynomial <@ polynomial__multiply (polynomial, start, step_by,
      (truncateu32 zeta_0));
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_at_layer_7_and_6 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var sTEP_BY_7:int;
    var sTEP_BY_6:int;
    var zETA_7:int;
    var zETA_60:int;
    var zETA_61:int;
    sTEP_BY_7 <- (2 * 8);
    sTEP_BY_6 <- ((1 `<<` 6) %/ 8);
    zETA_7 <- 25847;
    zETA_60 <- (- 2608894);
    zETA_61 <- (- 518909);
    polynomial <@ polynomial____layer (polynomial, 0, sTEP_BY_7, zETA_7);
    polynomial <@ polynomial____layer (polynomial, 8, sTEP_BY_7, zETA_7);
    polynomial <@ polynomial____layer (polynomial, 0, sTEP_BY_6, zETA_60);
    polynomial <@ polynomial____layer (polynomial, 16, sTEP_BY_6, zETA_61);
    polynomial <@ polynomial____layer (polynomial, 4, sTEP_BY_7, zETA_7);
    polynomial <@ polynomial____layer (polynomial, 12, sTEP_BY_7, zETA_7);
    polynomial <@ polynomial____layer (polynomial, 4, sTEP_BY_6, zETA_60);
    polynomial <@ polynomial____layer (polynomial, 20, sTEP_BY_6, zETA_61);
    return polynomial;
  }
  proc polynomial__ntt (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    
    polynomial <@ polynomial__ntt_at_layer_7_and_6 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_5 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_4 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_3 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_2 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_1 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_0 (polynomial);
    return polynomial;
  }
  proc polynomial__invert_at_layer_0 (polynomial:W32.t Array256.t, start:int,
                                      zetas:W256.t) : W32.t Array256.t = {
    var coeffs_i:W256.t;
    var coeffs_i_plus_1:W256.t;
    var low_values:W256.t;
    var high_values:W256.t;
    var differences:W256.t;
    var sums:W256.t;
    var coeffs_i_start:int;
    var coeffs_i_plus_1_start:int;
    coeffs_i_start <- start;
    coeffs_i_start <- (coeffs_i_start * 32);
    coeffs_i <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_start);
    coeffs_i <- (VPSHUFD_256 coeffs_i (W8.of_int 216));
    coeffs_i_plus_1_start <- coeffs_i_start;
    coeffs_i_plus_1_start <- (coeffs_i_plus_1_start + 32);
    coeffs_i_plus_1 <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_plus_1_start);
    coeffs_i_plus_1 <- (VPSHUFD_256 coeffs_i_plus_1 (W8.of_int 216));
    low_values <- (VPUNPCKL_4u64 coeffs_i coeffs_i_plus_1);
    high_values <- (VPUNPCKH_4u64 coeffs_i coeffs_i_plus_1);
    differences <- (VPSUB_8u32 high_values low_values);
    sums <- (VPADD_8u32 high_values low_values);
    differences <@ montgomery_multiply_and_reduce (differences, zetas);
    coeffs_i <- (VPUNPCKL_4u64 sums differences);
    coeffs_i_plus_1 <- (VPUNPCKH_4u64 sums differences);
    coeffs_i <- (VPSHUFD_256 coeffs_i (W8.of_int 216));
    coeffs_i_plus_1 <- (VPSHUFD_256 coeffs_i_plus_1 (W8.of_int 216));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_start coeffs_i)));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_plus_1_start coeffs_i_plus_1)));
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_0 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var i:int;
    var zetas:W256.t;
    var start:int;
    i <- 0;
    while ((i < 16)) {
      start <- (i * 2);
      zetas <- zETAS_TO_INVERT_LAYER_0.[i];
      polynomial <@ polynomial__invert_at_layer_0 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_at_layer_1 (polynomial:W32.t Array256.t, start:int,
                                      zetas:W256.t) : W32.t Array256.t = {
    var coeffs_i:W256.t;
    var coeffs_i_plus_1:W256.t;
    var low_values:W256.t;
    var high_values:W256.t;
    var differences:W256.t;
    var sums:W256.t;
    var coeffs_i_start:int;
    var coeffs_i_plus_1_start:int;
    coeffs_i_start <- start;
    coeffs_i_start <- (coeffs_i_start * 32);
    coeffs_i <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_start);
    coeffs_i_plus_1_start <- coeffs_i_start;
    coeffs_i_plus_1_start <- (coeffs_i_plus_1_start + 32);
    coeffs_i_plus_1 <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_plus_1_start);
    low_values <- (VPUNPCKL_4u64 coeffs_i coeffs_i_plus_1);
    high_values <- (VPUNPCKH_4u64 coeffs_i coeffs_i_plus_1);
    differences <- (VPSUB_8u32 high_values low_values);
    sums <- (VPADD_8u32 high_values low_values);
    differences <@ montgomery_multiply_and_reduce (differences, zetas);
    coeffs_i <- (VPUNPCKL_4u64 sums differences);
    coeffs_i_plus_1 <- (VPUNPCKH_4u64 sums differences);
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_start coeffs_i)));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_plus_1_start coeffs_i_plus_1)));
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_1 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var i:int;
    var zetas:W256.t;
    var start:int;
    i <- 0;
    while ((i < 16)) {
      start <- (i * 2);
      zetas <- zETAS_TO_INVERT_LAYER_1.[i];
      polynomial <@ polynomial__invert_at_layer_1 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_at_layer_2 (polynomial:W32.t Array256.t, start:int,
                                      zetas:W256.t) : W32.t Array256.t = {
    var coeffs_i:W256.t;
    var coeffs_i_plus_1:W256.t;
    var low_values:W256.t;
    var high_values:W256.t;
    var differences:W256.t;
    var sums:W256.t;
    var coeffs_i_start:int;
    var coeffs_i_plus_1_start:int;
    coeffs_i_start <- start;
    coeffs_i_start <- (coeffs_i_start * 32);
    coeffs_i <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_start);
    coeffs_i_plus_1_start <- coeffs_i_start;
    coeffs_i_plus_1_start <- (coeffs_i_plus_1_start + 32);
    coeffs_i_plus_1 <-
    (get256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_plus_1_start);
    low_values <- (VPERM2I128 coeffs_i coeffs_i_plus_1 (W8.of_int 32));
    high_values <- (VPERM2I128 coeffs_i coeffs_i_plus_1 (W8.of_int 49));
    differences <- (VPSUB_8u32 high_values low_values);
    sums <- (VPADD_8u32 high_values low_values);
    differences <@ montgomery_multiply_and_reduce (differences, zetas);
    coeffs_i <- (VPERM2I128 sums differences (W8.of_int 32));
    coeffs_i_plus_1 <- (VPERM2I128 sums differences (W8.of_int 49));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_start coeffs_i)));
    polynomial <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
    coeffs_i_plus_1_start coeffs_i_plus_1)));
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_2 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var i:int;
    var zetas:W256.t;
    var start:int;
    i <- 0;
    while ((i < 16)) {
      start <- (i * 2);
      zetas <- zETAS_TO_INVERT_LAYER_2.[i];
      polynomial <@ polynomial__invert_at_layer_2 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_round (polynomial:W32.t Array256.t, offset:int,
                                     step_by:int, zeta_0:W32.t) : W32.t Array256.t = {
    var zetas:W256.t;
    var coeffs_i:W256.t;
    var coeffs_i_plus_step_by:W256.t;
    var a_minus_b:W256.t;
    var i:int;
    var index_i:int;
    var index_i_plus_step_by:int;
    zetas <- (zeroextu256 (VMOV_32 zeta_0));
    zetas <- (VPBROADCAST_8u32 (truncateu32 zetas));
    i <- offset;
    offset <- (offset + step_by);
    while ((i < offset)) {
      index_i <- i;
      index_i <- (index_i * 32);
      coeffs_i <-
      (get256_direct (WArray1024.init32 (fun i_0 => polynomial.[i_0]))
      index_i);
      index_i_plus_step_by <- i;
      index_i_plus_step_by <- (index_i_plus_step_by + step_by);
      index_i_plus_step_by <- (index_i_plus_step_by * 32);
      coeffs_i_plus_step_by <-
      (get256_direct (WArray1024.init32 (fun i_0 => polynomial.[i_0]))
      index_i_plus_step_by);
      a_minus_b <- (VPSUB_8u32 coeffs_i_plus_step_by coeffs_i);
      coeffs_i <- (VPADD_8u32 coeffs_i coeffs_i_plus_step_by);
      coeffs_i_plus_step_by <@ montgomery_multiply_and_reduce (a_minus_b,
      zetas);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct
      (WArray1024.init32 (fun i_0 => polynomial.[i_0])) index_i coeffs_i)));
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct
      (WArray1024.init32 (fun i_0 => polynomial.[i_0])) index_i_plus_step_by
      coeffs_i_plus_step_by)));
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_3 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var zeta_0:W32.t;
    var offset:int;
    var step_by:int;
    sTEP <- 8;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 16)) {
      offset <- (((i * sTEP) * 2) %/ 8);
      step_by <- sTEP_BY;
      zeta_0 <- zETAS_TO_INVERT_LAYER_3.[i];
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_4 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var zeta_0:W32.t;
    var offset:int;
    var step_by:int;
    sTEP <- 16;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 8)) {
      offset <- (((i * sTEP) * 2) %/ 8);
      step_by <- sTEP_BY;
      zeta_0 <- zETAS_TO_INVERT_LAYER_4.[i];
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_5 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var zeta_0:W32.t;
    var offset:int;
    var step_by:int;
    sTEP <- 32;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 4)) {
      offset <- (((i * sTEP) * 2) %/ 8);
      step_by <- sTEP_BY;
      zeta_0 <- zETAS_TO_INVERT_LAYER_5.[i];
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_6 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var zeta_0:W32.t;
    var offset:int;
    var step_by:int;
    sTEP <- 64;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 2)) {
      offset <- (((i * sTEP) * 2) %/ 8);
      step_by <- sTEP_BY;
      zeta_0 <- zETAS_TO_INVERT_LAYER_6.[i];
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_7 (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var zeta_0:W32.t;
    var offset:int;
    var step_by:int;
    sTEP <- 128;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 1)) {
      offset <- (((i * sTEP) * 2) %/ 8);
      step_by <- sTEP_BY;
      zeta_0 <- (W32.of_int 25847);
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_montgomery (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var temp:W64.t;
    var twiddle_factors:W256.t;
    var coefficients:W256.t;
    var i:int;
    polynomial <@ polynomial__invert_ntt_at_layer_0 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_1 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_2 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_3 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_4 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_5 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_6 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_7 (polynomial);
    temp <- (W64.of_int 41978);
    twiddle_factors <- (zeroextu256 (VMOV_32 (truncateu32 temp)));
    twiddle_factors <- (VPBROADCAST_8u32 (truncateu32 twiddle_factors));
    i <- 0;
    while ((i < ((256 * 32) %/ 8))) {
      coefficients <-
      (get256_direct (WArray1024.init32 (fun i_0 => polynomial.[i_0])) i);
      coefficients <@ montgomery_multiply_and_reduce (coefficients,
      twiddle_factors);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct
      (WArray1024.init32 (fun i_0 => polynomial.[i_0])) i coefficients)));
      i <- (i + 32);
    }
    return polynomial;
  }
  proc __keccakf1600_pround_avx2 (state:W256.t Array7.t) : W256.t Array7.t = {
    var c00:W256.t;
    var c14:W256.t;
    var t2:W256.t;
    var t4:W256.t;
    var t0:W256.t;
    var t1:W256.t;
    var d14:W256.t;
    var d00:W256.t;
    var t3:W256.t;
    var t5:W256.t;
    var t6:W256.t;
    var t7:W256.t;
    var t8:W256.t;
    c00 <-
    (VPSHUFD_256 state.[2]
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    c14 <- (state.[5] `^` state.[3]);
    t2 <- (state.[4] `^` state.[6]);
    c14 <- (c14 `^` state.[1]);
    c14 <- (c14 `^` t2);
    t4 <-
    (VPERMQ c14
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    c00 <- (c00 `^` state.[2]);
    t0 <-
    (VPERMQ c00
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    t1 <- (c14 \vshr64u256 (W128.of_int 63));
    t2 <- (c14 \vadd64u256 c14);
    t1 <- (t1 `|` t2);
    d14 <-
    (VPERMQ t1
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    d00 <- (t1 `^` t4);
    d00 <-
    (VPERMQ d00
    (W8.of_int
    ((0 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    c00 <- (c00 `^` state.[0]);
    c00 <- (c00 `^` t0);
    t0 <- (c00 \vshr64u256 (W128.of_int 63));
    t1 <- (c00 \vadd64u256 c00);
    t1 <- (t1 `|` t0);
    state.[2] <- (state.[2] `^` d00);
    state.[0] <- (state.[0] `^` d00);
    d14 <-
    (VPBLEND_8u32 d14 t1
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t4 <-
    (VPBLEND_8u32 t4 c00
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    d14 <- (d14 `^` t4);
    t3 <- (VPSLLV_4u64 state.[2] kECCAK_RHOTATES_LEFT.[0]);
    state.[2] <- (VPSRLV_4u64 state.[2] kECCAK_RHOTATES_RIGHT.[0]);
    state.[2] <- (state.[2] `|` t3);
    state.[3] <- (state.[3] `^` d14);
    t4 <- (VPSLLV_4u64 state.[3] kECCAK_RHOTATES_LEFT.[2]);
    state.[3] <- (VPSRLV_4u64 state.[3] kECCAK_RHOTATES_RIGHT.[2]);
    state.[3] <- (state.[3] `|` t4);
    state.[4] <- (state.[4] `^` d14);
    t5 <- (VPSLLV_4u64 state.[4] kECCAK_RHOTATES_LEFT.[3]);
    state.[4] <- (VPSRLV_4u64 state.[4] kECCAK_RHOTATES_RIGHT.[3]);
    state.[4] <- (state.[4] `|` t5);
    state.[5] <- (state.[5] `^` d14);
    t6 <- (VPSLLV_4u64 state.[5] kECCAK_RHOTATES_LEFT.[4]);
    state.[5] <- (VPSRLV_4u64 state.[5] kECCAK_RHOTATES_RIGHT.[4]);
    state.[5] <- (state.[5] `|` t6);
    state.[6] <- (state.[6] `^` d14);
    t3 <-
    (VPERMQ state.[2]
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    t4 <-
    (VPERMQ state.[3]
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    t7 <- (VPSLLV_4u64 state.[6] kECCAK_RHOTATES_LEFT.[5]);
    t1 <- (VPSRLV_4u64 state.[6] kECCAK_RHOTATES_RIGHT.[5]);
    t1 <- (t1 `|` t7);
    state.[1] <- (state.[1] `^` d14);
    t5 <-
    (VPERMQ state.[4]
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    t6 <-
    (VPERMQ state.[5]
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    t8 <- (VPSLLV_4u64 state.[1] kECCAK_RHOTATES_LEFT.[1]);
    t2 <- (VPSRLV_4u64 state.[1] kECCAK_RHOTATES_RIGHT.[1]);
    t2 <- (t2 `|` t8);
    t7 <- (VPSRLDQ_256 t1 (W8.of_int 8));
    t0 <- ((invw t1) `&` t7);
    state.[3] <-
    (VPBLEND_8u32 t2 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t4 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[5] <-
    (VPBLEND_8u32 t3 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t2 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[3] <-
    (VPBLEND_8u32 state.[3] t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t8 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[5] <-
    (VPBLEND_8u32 state.[5] t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[3] <-
    (VPBLEND_8u32 state.[3] t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t8 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[5] <-
    (VPBLEND_8u32 state.[5] t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[3] <- ((invw state.[3]) `&` t8);
    state.[5] <- ((invw state.[5]) `&` t7);
    state.[6] <-
    (VPBLEND_8u32 t5 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t3 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[3] <- (state.[3] `^` t3);
    state.[6] <-
    (VPBLEND_8u32 state.[6] t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t8 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[5] <- (state.[5] `^` t5);
    state.[6] <-
    (VPBLEND_8u32 state.[6] t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t8 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[6] <- ((invw state.[6]) `&` t8);
    state.[6] <- (state.[6] `^` t6);
    state.[4] <-
    (VPERMQ t1
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    t8 <-
    (VPBLEND_8u32 state.[4] state.[0]
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[1] <-
    (VPERMQ t1
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    state.[1] <-
    (VPBLEND_8u32 state.[1] state.[0]
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[1] <- ((invw state.[1]) `&` t8);
    state.[2] <-
    (VPBLEND_8u32 t4 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t6 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[2] <-
    (VPBLEND_8u32 state.[2] t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[2] <-
    (VPBLEND_8u32 state.[2] t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[2] <- ((invw state.[2]) `&` t7);
    state.[2] <- (state.[2] `^` t2);
    t0 <-
    (VPERMQ t0
    (W8.of_int
    ((0 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    state.[3] <-
    (VPERMQ state.[3]
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    state.[5] <-
    (VPERMQ state.[5]
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    state.[6] <-
    (VPERMQ state.[6]
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    state.[4] <-
    (VPBLEND_8u32 t6 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t5 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[4] <-
    (VPBLEND_8u32 state.[4] t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[4] <-
    (VPBLEND_8u32 state.[4] t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[4] <- ((invw state.[4]) `&` t7);
    state.[0] <- (state.[0] `^` t0);
    state.[1] <- (state.[1] `^` t1);
    state.[4] <- (state.[4] `^` t4);
    return state;
  }
  proc __keccakf1600_avx2 (state:W256.t Array7.t) : W256.t Array7.t = {
    var round_constants:W64.t Array24.t;
    var rc:W256.t;
    var r:int;
    round_constants <- witness;
    round_constants <- kECCAK1600_RC;
    r <- 0;
    state <@ __keccakf1600_pround_avx2 (state);
    rc <- (VPBROADCAST_4u64 round_constants.[r]);
    state.[0] <- (state.[0] `^` rc);
    r <- (r + 1);
    while ((r < 24)) {
      state <@ __keccakf1600_pround_avx2 (state);
      rc <- (VPBROADCAST_4u64 round_constants.[r]);
      state.[0] <- (state.[0] `^` rc);
      r <- (r + 1);
    }
    return state;
  }
  proc _keccakf1600_avx2 (state:W256.t Array7.t) : W256.t Array7.t = {
    
    state <@ __keccakf1600_avx2 (state);
    return state;
  }
  proc __stavx2_pack (st:W64.t Array25.t) : W256.t Array7.t = {
    var state:W256.t Array7.t;
    var t128_1:W128.t;
    var t128_0:W128.t;
    var r:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    state <- witness;
    state.[0] <-
    (VPBROADCAST_4u64
    (get64_direct (WArray200.init64 (fun i => st.[i])) (8 * 0)));
    state.[1] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (1 * 8));
    t128_1 <- (VMOV_64 st.[5]);
    state.[3] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (6 * 8));
    t128_0 <- (VMOV_64 st.[10]);
    state.[4] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (11 * 8));
    r <- st.[15];
    t128_1 <- (VPINSR_2u64 t128_1 r (W8.of_int 1));
    state.[5] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (16 * 8));
    r <- st.[20];
    t128_0 <- (VPINSR_2u64 t128_0 r (W8.of_int 1));
    t256_0 <- (zeroextu256 t128_0);
    t256_0 <- (VINSERTI128 t256_0 t128_1 (W8.of_int 1));
    state.[2] <- t256_0;
    state.[6] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (21 * 8));
    t256_0 <-
    (VPBLEND_8u32 state.[3] state.[5]
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_1 <-
    (VPBLEND_8u32 state.[6] state.[4]
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_2 <-
    (VPBLEND_8u32 state.[4] state.[3]
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[3] <-
    (VPBLEND_8u32 t256_0 t256_1
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[4] <-
    (VPBLEND_8u32 t256_1 t256_0
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_0 <-
    (VPBLEND_8u32 state.[5] state.[6]
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[5] <-
    (VPBLEND_8u32 t256_0 t256_2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[6] <-
    (VPBLEND_8u32 t256_2 t256_0
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    return state;
  }
  proc __stavx2_unpack (st:W64.t Array25.t, state:W256.t Array7.t) : 
  W64.t Array25.t = {
    var t128_0:W128.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t128_1:W128.t;
    var t256_4:W256.t;
    t128_0 <- (truncateu128 state.[0]);
    st.[0] <- (VMOVLPD t128_0);
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (1 * 8)
    state.[1])));
    t256_0 <-
    (VPBLEND_8u32 state.[3] state.[4]
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_1 <-
    (VPBLEND_8u32 state.[4] state.[3]
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_2 <-
    (VPBLEND_8u32 state.[5] state.[6]
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_3 <-
    (VPBLEND_8u32 state.[6] state.[5]
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t128_1 <- (VEXTRACTI128 state.[2] (W8.of_int 1));
    st.[5] <- (VMOVLPD t128_1);
    t256_4 <-
    (VPBLEND_8u32 t256_0 t256_3
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (6 * 8)
    t256_4)));
    t128_0 <- (truncateu128 state.[2]);
    st.[10] <- (VMOVLPD t128_0);
    t256_4 <-
    (VPBLEND_8u32 t256_3 t256_1
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (11 * 8)
    t256_4)));
    st.[15] <- (VMOVHPD t128_1);
    t256_4 <-
    (VPBLEND_8u32 t256_2 t256_0
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (16 * 8)
    t256_4)));
    st.[20] <- (VMOVHPD t128_0);
    t256_4 <-
    (VPBLEND_8u32 t256_1 t256_2
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (21 * 8)
    t256_4)));
    return st;
  }
  proc _keccakf1600_st25_avx2 (st25:W64.t Array25.t) : W64.t Array25.t = {
    var state:W256.t Array7.t;
    state <- witness;
    state <@ __stavx2_pack (st25);
    state <@ __keccakf1600_avx2 (state);
    st25 <@ __stavx2_unpack (st25, state);
    return st25;
  }
  proc __SHLQ (x:W64.t, shbytes:int) : W64.t = {
    
    if ((shbytes <> 0)) {
      x <- (x `<<` (W8.of_int (8 * shbytes)));
    } else {
      
    }
    return x;
  }
  proc __SHLDQ (x:W128.t, shbytes:int) : W128.t = {
    
    if ((shbytes <> 0)) {
      x <- (VPSLLDQ_128 x (W8.of_int shbytes));
    } else {
      
    }
    return x;
  }
  proc __SHLQ_256 (x:W256.t, shbytes:int) : W256.t = {
    
    if ((shbytes <> 0)) {
      x <- (VPSLL_4u64 x (W128.of_int (8 * shbytes)));
    } else {
      
    }
    return x;
  }
  proc __m_rlen_read_upto8 (buf:int, len:int) : int * W64.t = {
    var w:W64.t;
    var zf:bool;
    var sh:W8.t;
    var x:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    if ((8 <= len)) {
      w <- (loadW64 Glob.mem buf);
      buf <- (buf + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        w <- (zeroextu64 (loadW32 Glob.mem buf));
        buf <- (buf + 4);
        sh <- (W8.of_int 32);
      } else {
        w <- (W64.of_int 0);
        sh <- (W8.of_int 0);
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        x <- (zeroextu64 (loadW16 Glob.mem buf));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        buf <- (buf + 2);
        sh <- (sh + (W8.of_int 16));
      } else {
        
      }
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        x <- (zeroextu64 (loadW8 Glob.mem buf));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        buf <- (buf + 1);
      } else {
        
      }
    }
    return (buf, w);
  }
  proc __u64_to_u256 (x:W64.t, l:int) : W256.t = {
    var t256:W256.t;
    var t128:W128.t;
    if (((l %% 2) = 0)) {
      t128 <- (VMOV_64 x);
    } else {
      t128 <- (set0_128);
      t128 <- (VPINSR_2u64 t128 x (W8.of_int 1));
    }
    t256 <- (set0_256);
    if (((l %/ 2) = 0)) {
      t256 <- (VINSERTI128 t256 t128 (W8.of_int 0));
    } else {
      t256 <- (VINSERTI128 t256 t128 (W8.of_int 1));
    }
    return t256;
  }
  proc __state_init_avx2 () : W256.t Array7.t = {
    var st:W256.t Array7.t;
    var i:int;
    st <- witness;
    i <- 0;
    while ((i < 7)) {
      st.[i] <- (set0_256);
      i <- (i + 1);
    }
    return st;
  }
  proc __perm_reg3456_avx2 (r3:W256.t, r4:W256.t, r5:W256.t, r6:W256.t) : 
  W256.t * W256.t * W256.t * W256.t = {
    var st3:W256.t;
    var st4:W256.t;
    var st5:W256.t;
    var st6:W256.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    t256_0 <-
    (VPBLEND_8u32 r3 r5
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_1 <-
    (VPBLEND_8u32 r6 r4
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_2 <-
    (VPBLEND_8u32 r4 r3
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st3 <-
    (VPBLEND_8u32 t256_0 t256_1
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st4 <-
    (VPBLEND_8u32 t256_1 t256_0
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_0 <-
    (VPBLEND_8u32 r5 r6
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st5 <-
    (VPBLEND_8u32 t256_0 t256_2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st6 <-
    (VPBLEND_8u32 t256_2 t256_0
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    return (st3, st4, st5, st6);
  }
  proc __addstate_r3456_avx2 (st:W256.t Array7.t, r3:W256.t, r4:W256.t,
                              r5:W256.t, r6:W256.t) : W256.t Array7.t = {
    
    (r3, r4, r5, r6) <@ __perm_reg3456_avx2 (r3, r4, r5, r6);
    st.[3] <- (st.[3] `^` r3);
    st.[4] <- (st.[4] `^` r4);
    st.[5] <- (st.[5] `^` r5);
    st.[6] <- (st.[6] `^` r6);
    return st;
  }
  proc __stavx2_pos_avx2 (pOS:int) : int * int = {
    var r:int;
    var l:int;
    r <- 0;
    l <- 0;
    if ((0 < pOS)) {
      if ((pOS <= 4)) {
        r <- 1;
        l <- (pOS - 1);
      } else {
        if ((pOS = 10)) {
          r <- 2;
          l <- 0;
        } else {
          if ((pOS = 20)) {
            r <- 2;
            l <- 1;
          } else {
            if ((pOS = 5)) {
              r <- 2;
              l <- 2;
            } else {
              if ((pOS = 15)) {
                r <- 2;
                l <- 3;
              } else {
                if ((pOS = 16)) {
                  r <- 3;
                  l <- 0;
                } else {
                  if ((pOS = 7)) {
                    r <- 3;
                    l <- 1;
                  } else {
                    if ((pOS = 23)) {
                      r <- 3;
                      l <- 2;
                    } else {
                      if ((pOS = 14)) {
                        r <- 3;
                        l <- 3;
                      } else {
                        if ((pOS = 11)) {
                          r <- 4;
                          l <- 0;
                        } else {
                          if ((pOS = 22)) {
                            r <- 4;
                            l <- 1;
                          } else {
                            if ((pOS = 8)) {
                              r <- 4;
                              l <- 2;
                            } else {
                              if ((pOS = 19)) {
                                r <- 4;
                                l <- 3;
                              } else {
                                if ((pOS = 21)) {
                                  r <- 5;
                                  l <- 0;
                                } else {
                                  if ((pOS = 17)) {
                                    r <- 5;
                                    l <- 1;
                                  } else {
                                    if ((pOS = 13)) {
                                      r <- 5;
                                      l <- 2;
                                    } else {
                                      if ((pOS = 9)) {
                                        r <- 5;
                                        l <- 3;
                                      } else {
                                        if ((pOS = 6)) {
                                          r <- 6;
                                          l <- 0;
                                        } else {
                                          if ((pOS = 12)) {
                                            r <- 6;
                                            l <- 1;
                                          } else {
                                            if ((pOS = 18)) {
                                              r <- 6;
                                              l <- 2;
                                            } else {
                                              if ((pOS = 24)) {
                                                r <- 6;
                                                l <- 3;
                                              } else {
                                                
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    } else {
      
    }
    return (r, l);
  }
  proc __addratebit_avx2 (st:W256.t Array7.t, rATE_8:int) : W256.t Array7.t = {
    var t64:W64.t;
    var r:int;
    var l:int;
    var t256:W256.t;
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * rATE_8) - 1) %% 64)));
    (r, l) <@ __stavx2_pos_avx2 (((rATE_8 - 1) %/ 8));
    if ((r = 0)) {
      t256 <- (VPBROADCAST_4u64 t64);
    } else {
      t256 <@ __u64_to_u256 (t64, l);
    }
    st.[r] <- (st.[r] `^` t256);
    return st;
  }
  proc __4u64x4_u256x4 (y0:W256.t, y1:W256.t, y2:W256.t, y3:W256.t) : 
  W256.t * W256.t * W256.t * W256.t = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    x0 <- (VPERM2I128 y0 y2 (W8.of_int 32));
    x1 <- (VPERM2I128 y1 y3 (W8.of_int 32));
    x2 <- (VPERM2I128 y0 y2 (W8.of_int 49));
    x3 <- (VPERM2I128 y1 y3 (W8.of_int 49));
    y0 <- (VPUNPCKL_4u64 x0 x1);
    y1 <- (VPUNPCKH_4u64 x0 x1);
    y2 <- (VPUNPCKL_4u64 x2 x3);
    y3 <- (VPUNPCKH_4u64 x2 x3);
    return (y0, y1, y2, y3);
  }
  proc __f1600_loopbody_native (st:W256.t Array25.t, rol8:W256.t Array1.t,
                                rol56:W256.t Array1.t, rC:W64.t Array24.t,
                                i:int, y10:W256.t, y14:W256.t, y8:W256.t,
                                y15:W256.t, y9:W256.t, y13:W256.t, y3:W256.t,
                                y7:W256.t, y2:W256.t) : W256.t Array25.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t = {
    var i0:int;
    var i1:int;
    var i2:int;
    var i3:int;
    var i4:int;
    var i5:int;
    var i6:int;
    var i7:int;
    var i8:int;
    var i9:int;
    var i10:int;
    var i11:int;
    var i12:int;
    var i13:int;
    var i14:int;
    var i15:int;
    var i16:int;
    var i17:int;
    var i18:int;
    var i19:int;
    var i20:int;
    var i21:int;
    var i22:int;
    var i23:int;
    var y4:W256.t;
    var y0:W256.t;
    var y11:W256.t;
    var y12:W256.t;
    var y1:W256.t;
    var y6:W256.t;
    var y5:W256.t;
    i0 <- 0;
    i1 <- 1;
    i2 <- 2;
    i3 <- 3;
    i4 <- 4;
    i5 <- 5;
    i6 <- 6;
    i7 <- 9;
    i8 <- 10;
    i9 <- 13;
    i10 <- 14;
    i11 <- 16;
    i12 <- 17;
    i13 <- 19;
    i14 <- 20;
    i15 <- 23;
    i16 <- 7;
    i17 <- 8;
    i18 <- 11;
    i19 <- 12;
    i20 <- 15;
    i21 <- 18;
    i22 <- 21;
    i23 <- 22;
    y4 <- st.[i5];
    y0 <- (y9 `^` st.[i14]);
    st.[i16] <- y9;
    y9 <- y10;
    y11 <- st.[i6];
    y12 <- st.[i11];
    st.[i18] <- y3;
    y1 <- (y4 `^` st.[i8]);
    y10 <- st.[i2];
    st.[i17] <- y4;
    y12 <- (y12 `^` y3);
    y6 <- st.[i1];
    y4 <- st.[i10];
    st.[i21] <- y14;
    y0 <- (y0 `^` y1);
    y1 <- (y11 `^` y8);
    y11 <- (y7 `^` st.[i12]);
    st.[i20] <- y10;
    y12 <- (y12 `^` y1);
    y1 <- (y9 `^` y15);
    y3 <- st.[i7];
    st.[i19] <- y8;
    y11 <- (y11 `^` y1);
    y1 <- (y14 `^` st.[i9]);
    y12 <- (y12 `^` y6);
    y8 <- st.[i3];
    y11 <- (y11 `^` y10);
    y10 <- (y13 `^` st.[i15]);
    y3 <- (y3 `^` y4);
    st.[i22] <- y4;
    y4 <- (VPSRL_4u64 y12 (W128.of_int 63));
    y5 <- (VPSRL_4u64 y11 (W128.of_int 63));
    y0 <- (y0 `^` st.[i0]);
    y10 <- (y10 `^` y1);
    y1 <- st.[i4];
    y10 <- (y10 `^` y8);
    y14 <- y1;
    y1 <- (y2 `^` st.[i13]);
    st.[i23] <- y14;
    y1 <- (y1 `^` y3);
    y3 <- (VPSLL_4u64 y12 (W128.of_int 1));
    y3 <- (y3 `|` y4);
    y4 <- (VPSLL_4u64 y11 (W128.of_int 1));
    y1 <- (y1 `^` y14);
    y4 <- (y4 `|` y5);
    y14 <- (VPSRL_4u64 y10 (W128.of_int 63));
    y3 <- (y3 `^` y1);
    y5 <- (VPSLL_4u64 y10 (W128.of_int 1));
    y4 <- (y4 `^` y0);
    y5 <- (y5 `|` y14);
    y6 <- (y4 `^` y6);
    y5 <- (y5 `^` y12);
    y12 <- (VPSRL_4u64 y1 (W128.of_int 63));
    y1 <- (VPSLL_4u64 y1 (W128.of_int 1));
    y7 <- (y5 `^` y7);
    y9 <- (y5 `^` y9);
    y1 <- (y1 `|` y12);
    y12 <- (y3 `^` st.[i0]);
    y1 <- (y1 `^` y11);
    y11 <- (VPSRL_4u64 y0 (W128.of_int 63));
    y0 <- (VPSLL_4u64 y0 (W128.of_int 1));
    y13 <- (y1 `^` y13);
    y8 <- (y1 `^` y8);
    y0 <- (y0 `|` y11);
    y0 <- (y0 `^` y10);
    y10 <- (y4 `^` st.[i6]);
    y2 <- (y0 `^` y2);
    y11 <- (VPSRL_4u64 y10 (W128.of_int 20));
    y10 <- (VPSLL_4u64 y10 (W128.of_int 44));
    y10 <- (y10 `|` y11);
    y11 <- (y5 `^` y15);
    y15 <- (VPBROADCAST_4u64 rC.[(W64.to_uint (W64.of_int i))]);
    y14 <- (VPSRL_4u64 y11 (W128.of_int 21));
    y11 <- (VPSLL_4u64 y11 (W128.of_int 43));
    y11 <- (y11 `|` y14);
    y14 <- ((invw y10) `&` y11);
    y14 <- (y14 `^` y15);
    y15 <- (y14 `^` y12);
    y14 <- (VPSRL_4u64 y13 (W128.of_int 43));
    y13 <- (VPSLL_4u64 y13 (W128.of_int 21));
    st.[i0] <- y15;
    y13 <- (y13 `|` y14);
    y14 <- ((invw y11) `&` y13);
    y15 <- (y14 `^` y10);
    y14 <- (VPSRL_4u64 y2 (W128.of_int 50));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 14));
    st.[i1] <- y15;
    y2 <- (y2 `|` y14);
    y14 <- ((invw y13) `&` y2);
    y11 <- (y14 `^` y11);
    st.[i2] <- y11;
    y11 <- ((invw y2) `&` y12);
    y12 <- ((invw y12) `&` y10);
    y11 <- (y11 `^` y13);
    st.[i3] <- y11;
    y11 <- (y12 `^` y2);
    y2 <- (VPSRL_4u64 y8 (W128.of_int 36));
    y8 <- (VPSLL_4u64 y8 (W128.of_int 28));
    st.[i4] <- y11;
    y8 <- (y8 `|` y2);
    y2 <- (y0 `^` st.[i7]);
    y10 <- (VPSRL_4u64 y2 (W128.of_int 44));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 20));
    y2 <- (y2 `|` y10);
    y10 <- (y3 `^` st.[i8]);
    y11 <- (VPSRL_4u64 y10 (W128.of_int 61));
    y10 <- (VPSLL_4u64 y10 (W128.of_int 3));
    y10 <- (y10 `|` y11);
    y11 <- ((invw y2) `&` y10);
    y11 <- (y11 `^` y8);
    st.[i5] <- y11;
    y11 <- (y4 `^` st.[i11]);
    y12 <- (VPSRL_4u64 y11 (W128.of_int 19));
    y11 <- (VPSLL_4u64 y11 (W128.of_int 45));
    y11 <- (y11 `|` y12);
    y12 <- ((invw y10) `&` y11);
    y12 <- (y12 `^` y2);
    st.[i6] <- y12;
    y12 <- (VPSRL_4u64 y7 (W128.of_int 3));
    y7 <- (VPSLL_4u64 y7 (W128.of_int 61));
    y7 <- (y7 `|` y12);
    y12 <- ((invw y11) `&` y7);
    y10 <- (y12 `^` y10);
    y12 <- ((invw y7) `&` y8);
    y8 <- ((invw y8) `&` y2);
    y2 <- (VPSRL_4u64 y6 (W128.of_int 63));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 1));
    y14 <- (y12 `^` y11);
    y6 <- (y6 `|` y2);
    y2 <- (VPSRL_4u64 y9 (W128.of_int 58));
    y12 <- (y8 `^` y7);
    y9 <- (VPSLL_4u64 y9 (W128.of_int 6));
    st.[i7] <- y12;
    y7 <- (y0 `^` st.[i13]);
    y9 <- (y9 `|` y2);
    y2 <- (y1 `^` st.[i9]);
    y7 <- (VPSHUFB_256 y7 rol8.[0]);
    y11 <- (VPSRL_4u64 y2 (W128.of_int 39));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 25));
    y11 <- (y11 `|` y2);
    y2 <- ((invw y9) `&` y11);
    y8 <- ((invw y11) `&` y7);
    y12 <- (y2 `^` y6);
    y2 <- (y3 `^` st.[i14]);
    y8 <- (y8 `^` y9);
    st.[i8] <- y12;
    y12 <- (VPSRL_4u64 y2 (W128.of_int 46));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 18));
    y2 <- (y12 `|` y2);
    y12 <- ((invw y7) `&` y2);
    y15 <- (y12 `^` y11);
    y11 <- ((invw y2) `&` y6);
    y6 <- ((invw y6) `&` y9);
    y12 <- (y11 `^` y7);
    st.[i9] <- y12;
    y12 <- (y6 `^` y2);
    y6 <- (y0 `^` st.[i23]);
    y0 <- (y0 `^` st.[i22]);
    st.[i10] <- y12;
    y2 <- (VPSRL_4u64 y6 (W128.of_int 37));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 27));
    y2 <- (y2 `|` y6);
    y6 <- (y3 `^` st.[i17]);
    y3 <- (y3 `^` st.[i16]);
    y7 <- (VPSRL_4u64 y6 (W128.of_int 28));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 36));
    y7 <- (y7 `|` y6);
    y6 <- (y4 `^` st.[i19]);
    y4 <- (y4 `^` st.[i18]);
    y12 <- (VPSRL_4u64 y6 (W128.of_int 54));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 10));
    y12 <- (y12 `|` y6);
    y6 <- (y5 `^` st.[i12]);
    y5 <- (y5 `^` st.[i20]);
    y9 <- ((invw y7) `&` y12);
    y11 <- (VPSRL_4u64 y6 (W128.of_int 49));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 15));
    y9 <- (y9 `^` y2);
    y11 <- (y11 `|` y6);
    y6 <- ((invw y12) `&` y11);
    y6 <- (y6 `^` y7);
    st.[i11] <- y6;
    y6 <- (y1 `^` st.[i15]);
    y1 <- (y1 `^` st.[i21]);
    y6 <- (VPSHUFB_256 y6 rol56.[0]);
    y13 <- ((invw y11) `&` y6);
    y13 <- (y13 `^` y12);
    st.[i12] <- y13;
    y13 <- ((invw y6) `&` y2);
    y2 <- ((invw y2) `&` y7);
    y2 <- (y2 `^` y6);
    y6 <- (VPSRL_4u64 y4 (W128.of_int 62));
    y13 <- (y13 `^` y11);
    st.[i13] <- y2;
    y2 <- (VPSRL_4u64 y5 (W128.of_int 2));
    y5 <- (VPSLL_4u64 y5 (W128.of_int 62));
    y2 <- (y2 `|` y5);
    y5 <- (VPSRL_4u64 y1 (W128.of_int 9));
    y1 <- (VPSLL_4u64 y1 (W128.of_int 55));
    y4 <- (VPSLL_4u64 y4 (W128.of_int 2));
    y1 <- (y5 `|` y1);
    y5 <- (VPSRL_4u64 y0 (W128.of_int 25));
    y4 <- (y6 `|` y4);
    y0 <- (VPSLL_4u64 y0 (W128.of_int 39));
    y5 <- (y5 `|` y0);
    y0 <- ((invw y1) `&` y5);
    y0 <- (y0 `^` y2);
    st.[i14] <- y0;
    y0 <- (VPSRL_4u64 y3 (W128.of_int 23));
    y3 <- (VPSLL_4u64 y3 (W128.of_int 41));
    y0 <- (y0 `|` y3);
    y7 <- ((invw y0) `&` y4);
    y3 <- ((invw y5) `&` y0);
    y7 <- (y7 `^` y5);
    y5 <- ((invw y4) `&` y2);
    y2 <- ((invw y2) `&` y1);
    y5 <- (y5 `^` y0);
    y3 <- (y3 `^` y1);
    y2 <- (y2 `^` y4);
    st.[i15] <- y5;
    return (st, y10, y14, y8, y15, y9, y13, y3, y7, y2);
  }
  proc __regs_fetch (st:W256.t Array25.t) : W256.t * W256.t * W256.t *
                                            W256.t * W256.t * W256.t *
                                            W256.t * W256.t * W256.t = {
    var y10:W256.t;
    var y14:W256.t;
    var y8:W256.t;
    var y15:W256.t;
    var y9:W256.t;
    var y13:W256.t;
    var y3:W256.t;
    var y7:W256.t;
    var y2:W256.t;
    y10 <- st.[7];
    y14 <- st.[8];
    y8 <- st.[11];
    y15 <- st.[12];
    y9 <- st.[15];
    y13 <- st.[18];
    y3 <- st.[21];
    y7 <- st.[22];
    y2 <- st.[24];
    return (y10, y14, y8, y15, y9, y13, y3, y7, y2);
  }
  proc __regs_unfetch (st:W256.t Array25.t, y10:W256.t, y14:W256.t,
                       y8:W256.t, y15:W256.t, y9:W256.t, y13:W256.t,
                       y3:W256.t, y7:W256.t, y2:W256.t) : W256.t Array25.t = {
    
    st.[7] <- y10;
    st.[8] <- y14;
    st.[11] <- y8;
    st.[12] <- y15;
    st.[15] <- y9;
    st.[18] <- y13;
    st.[21] <- y3;
    st.[22] <- y7;
    st.[24] <- y2;
    return st;
  }
  proc __keccakf1600_avx2x4_native (st:W256.t Array25.t) : W256.t Array25.t = {
    var y10:W256.t;
    var y14:W256.t;
    var y8:W256.t;
    var y15:W256.t;
    var y9:W256.t;
    var y13:W256.t;
    var y3:W256.t;
    var y7:W256.t;
    var y2:W256.t;
    var rol8:W256.t Array1.t;
    var rol56:W256.t Array1.t;
    var rc:W64.t Array24.t;
    var i:int;
    rc <- witness;
    rol56 <- witness;
    rol8 <- witness;
    (y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ __regs_fetch (st);
    rol8 <- rOL8;
    rol56 <- rOL56;
    rc <- kECCAK1600_RC;
    i <- 0;
    (st, y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ __f1600_loopbody_native (
    st, rol8, rol56, rc, i, y10, y14, y8, y15, y9, y13, y3, y7, y2);
    i <- (i + 1);
    while ((i < 24)) {
      (st, y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ __f1600_loopbody_native (
      st, rol8, rol56, rc, i, y10, y14, y8, y15, y9, y13, y3, y7, y2);
      i <- (i + 1);
    }
    st <@ __regs_unfetch (st, y10, y14, y8, y15, y9, y13, y3, y7, y2);
    return st;
  }
  proc __keccakf1600_avx2x4 (a:W256.t Array25.t) : W256.t Array25.t = {
    
    a <@ __keccakf1600_avx2x4_native (a);
    return a;
  }
  proc _keccakf1600_avx2x4 (a:W256.t Array25.t) : W256.t Array25.t = {
    
    a <@ __keccakf1600_avx2x4 (a);
    return a;
  }
  proc __state_init_avx2x4 (st:W256.t Array25.t) : W256.t Array25.t = {
    var z256:W256.t;
    var i:int;
    z256 <- (set0_256);
    i <- 0;
    while ((i < (32 * 25))) {
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i_0 => st.[i_0])) 
      i z256)));
      i <- (i + 32);
    }
    return st;
  }
  proc __addratebit_avx2x4 (st:W256.t Array25.t, rATE8:int) : W256.t Array25.t = {
    var t64:W64.t;
    var t128:W128.t;
    var t256:W256.t;
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * rATE8) - 1) %% 64)));
    t128 <- (VMOV_64 t64);
    t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
    t256 <- (t256 `^` st.[((rATE8 - 1) %/ 8)]);
    st.[((rATE8 - 1) %/ 8)] <- t256;
    return st;
  }
  proc _init_updstate_avx2 (st:W64.t Array26.t, r64:int, trailb:W8.t) : 
  W64.t Array26.t = {
    var r256:W256.t;
    var i:int;
    var status:W64.t;
    var t:W64.t;
    r256 <- (set0_256);
    i <- 0;
    while ((i < 6)) {
      st <-
      (Array26.init
      (WArray208.get64
      (WArray208.set256 (WArray208.init64 (fun i_0 => st.[i_0])) i r256)));
      i <- (i + 1);
    }
    st.[24] <- (W64.of_int 0);
    status <- (zeroextu64 trailb);
    status <- (status `<<` (W8.of_int 8));
    r64 <- (W8.to_uint ((W8.of_int r64) - (W8.of_int 1)));
    t <- (zeroextu64 (W8.of_int r64));
    status <- (status + t);
    status <- (status `<<` (W8.of_int 8));
    st.[25] <- status;
    return st;
  }
  proc _ststatus_data (ststatus:W64.t) : W8.t * int * int = {
    var trailb:W8.t;
    var at:W64.t;
    var r8:W64.t;
    var c_200:W64.t;
    var c_0:W64.t;
    var r8_ui:int;
    var at_ui:int;
    at <- ststatus;
    at <- (at `&` (W64.of_int 255));
    ststatus <- (ststatus `>>` (W8.of_int 8));
    r8 <- ststatus;
    r8 <- (r8 `&` (W64.of_int 255));
    r8 <- (r8 + (W64.of_int 1));
    r8 <- (r8 `<<` (W8.of_int 3));
    c_200 <- (W64.of_int 200);
    r8 <- (((W64.of_int 200) \ult r8) ? c_200 : r8);
    c_0 <- (W64.of_int 0);
    at <- ((r8 \ule at) ? c_0 : at);
    ststatus <- (ststatus `>>` (W8.of_int 8));
    trailb <- (truncateu8 ststatus);
    r8_ui <- (W64.to_uint r8);
    at_ui <- (W64.to_uint at);
    return (trailb, r8_ui, at_ui);
  }
  proc _finish_updstate_avx2 (st:W64.t Array26.t) : W64.t Array26.t = {
    var ststatus:W64.t;
    var trailb:W8.t;
    var r8:int;
    var at:int;
    ststatus <- st.[25];
    (trailb, r8, at) <@ _ststatus_data (ststatus);
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) at
    ((get8_direct (WArray208.init64 (fun i => st.[i])) at) `^` trailb))));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (r8 - 1)
    ((get8_direct (WArray208.init64 (fun i => st.[i])) (r8 - 1)) `^`
    (W8.of_int 128)))));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set32_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    ((get32_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)) `&`
    (W32.of_int 4278255360)))));
    return st;
  }
  proc _add_m_updstate_avx2 (st:W64.t Array25.t, at:int, buf:int, upto:int) : 
  W64.t Array25.t * int * int = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var upto8:W64.t;
    var len:int;
    var buf2:int;
    var newat:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      (buf2, t64) <@ __m_rlen_read_upto8 (buf, len);
      len <- (len + (W64.to_uint at8));
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
      if ((8 <= len)) {
        buf <- (buf + 8);
        buf <- (buf - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        buf <- buf2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (loadW64 Glob.mem buf);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
      at <- newat;
      buf <- (buf + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      (buf, t64) <@ __m_rlen_read_upto8 (buf, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
    } else {
      
    }
    at <- upto;
    return (st, at, buf);
  }
  proc _absorb_m_updstate_avx2 (st:W64.t Array26.t, buf:int, len:int) : 
  W64.t Array26.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var  _0:W8.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ _ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    len <- (len + at);
    while ((r8 <= len)) {
      (stk, at, buf) <@ _add_m_updstate_avx2 (stk, at, buf, r8);
      stk <@ _keccakf1600_st25_avx2 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (* Erased call to unspill *)
    (stk, at,  _1) <@ _add_m_updstate_avx2 (stk, at, buf, len);
    st <-
    (Array26.init
    (fun i => (if (0 <= i < (0 + 25)) then stk.[(i - 0)] else st.[i])));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    (truncateu8 (W64.of_int at)))));
    return st;
  }
  proc a2____a_ilen_read_upto8_at (buf:W8.t Array2.t, offset:int, dELTA:int,
                                   lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WArray2.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLQ (w, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray2.init8 (fun i => buf.[i])) (offset + dELTA)));
          w <@ __SHLQ (w, (aT - cUR));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray2.init8 (fun i => buf.[i])) (offset + dELTA)));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ __SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <-
          (zeroextu64
          (get8_direct (WArray2.init8 (fun i => buf.[i])) (offset + dELTA)));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          t8 <@ __SHLQ (t8, (aT - cUR));
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a2____a_ilen_read_upto16_at (buf:W8.t Array2.t, offset:int, dELTA:int,
                                    lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray2.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLDQ (w, (aT - cUR));
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a2____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t64_0) <@ a2____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a2____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a2____a_ilen_read_upto32_at (buf:W8.t Array2.t, offset:int, dELTA:int,
                                    lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WArray2.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a2____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t128_0) <@ a2____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a2____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a2____a_ilen_read_bcast_upto8_at (buf:W8.t Array2.t, offset:int,
                                         dELTA:int, lEN:int, tRAIL:int,
                                         cUR:int, aT:int) : int * int * int *
                                                            int * W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WArray2.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ __SHLQ_256 (w256, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        (dELTA, lEN, tRAIL, aT, w) <@ a2____a_ilen_read_upto8_at (buf,
        offset, dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc a2____addstate_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array2.t,
                            offset:int, _LEN:int, _TRAILB:int) : W256.t Array7.t *
                                                                 int * int = {
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, r0) <@ a2____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ a2____a_ilen_read_upto32_at (
      buf, offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ a2____a_ilen_read_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ a2____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ a2____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ a2____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ a2____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ a2____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ a2____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ a2____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {
      
    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc a2____absorb_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array2.t,
                          _TRAILB:int, _RATE8:int) : W256.t Array7.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 2;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a2____addstate_avx2 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a2____addstate_avx2 (st, 0, buf, offset, 
        _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a2____addstate_avx2 (st, aT, buf, offset, _LEN,
    _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a2____addstate_avx2x4 (st:W256.t Array25.t, aT:int,
                              buf0:W8.t Array2.t, buf1:W8.t Array2.t,
                              buf2:W8.t Array2.t, buf3:W8.t Array2.t,
                              offset:int, _LEN:int, _TRAILB:int) : W256.t Array25.t *
                                                                   int * int = {
    var dELTA:int;
    var aT8:int;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var at:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    var  _6:int;
    var  _7:int;
    var  _8:int;
    var  _9:int;
    var  _10:int;
    var  _11:int;
    var  _12:int;
    var  _13:int;
    var  _14:int;
    var  _15:int;
    var  _16:int;
    var  _17:int;
    var  _18:int;
    var  _19:int;
    var  _20:int;
    var  _21:int;
    var  _22:int;
    var  _23:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      ( _0,  _1,  _2,  _3, t0) <@ a2____a_ilen_read_upto8_at (buf0, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 0)) `^`
      t0))));
      ( _4,  _5,  _6,  _7, t1) <@ a2____a_ilen_read_upto8_at (buf1, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 1)) `^`
      t1))));
      ( _8,  _9,  _10,  _11, t2) <@ a2____a_ilen_read_upto8_at (buf2, 
      offset, dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 2)) `^`
      t2))));
      (dELTA, _LEN, _TRAILB, aT8, t3) <@ a2____a_ilen_read_upto8_at (
      buf3, offset, dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 3)) `^`
      t3))));
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (4 * (aT %/ 8));
    while ((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8))))) {
      t0 <- (get64_direct (WArray2.init8 (fun i => buf0.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      t1 <- (get64_direct (WArray2.init8 (fun i => buf1.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      t2 <- (get64_direct (WArray2.init8 (fun i => buf2.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      t3 <- (get64_direct (WArray2.init8 (fun i => buf3.[i])) offset);
      offset <- (offset + 8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 3)) `^` t3))));
      at <- (at + 4);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      ( _12,  _13,  _14,  _15, t0) <@ a2____a_ilen_read_upto8_at (buf0,
      offset, 0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      ( _16,  _17,  _18,  _19, t1) <@ a2____a_ilen_read_upto8_at (buf1,
      offset, 0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      ( _20,  _21,  _22,  _23, t2) <@ a2____a_ilen_read_upto8_at (buf2,
      offset, 0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      (dELTA, _LEN, _TRAILB, aT, t3) <@ a2____a_ilen_read_upto8_at (buf3,
      offset, 0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 3)) `^` t3))));
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc a2____absorb_avx2x4 (st:W256.t Array25.t, aT:int, buf0:W8.t Array2.t,
                            buf1:W8.t Array2.t, buf2:W8.t Array2.t,
                            buf3:W8.t Array2.t, _TRAILB:int, _RATE8:int) : 
  W256.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 2;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a2____addstate_avx2x4 (st, aT, buf0, buf1, 
      buf2, buf3, offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a2____addstate_avx2x4 (st, 0, buf0, buf1, 
        buf2, buf3, offset, _RATE8, 0);
        st <@ _keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a2____addstate_avx2x4 (st, aT, buf0, buf1, buf2, 
    buf3, offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a32____a_ilen_read_upto8_at (buf:W8.t Array32.t, offset:int,
                                    dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                    aT:int) : int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WArray32.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLQ (w, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray32.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          w <@ __SHLQ (w, (aT - cUR));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray32.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ __SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <-
          (zeroextu64
          (get8_direct (WArray32.init8 (fun i => buf.[i])) (offset + dELTA)));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          t8 <@ __SHLQ (t8, (aT - cUR));
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a32____a_ilen_read_upto16_at (buf:W8.t Array32.t, offset:int,
                                     dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                     aT:int) : int * int * int * int * W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray32.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLDQ (w, (aT - cUR));
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a32____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t64_0) <@ a32____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a32____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a32____a_ilen_read_upto32_at (buf:W8.t Array32.t, offset:int,
                                     dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                     aT:int) : int * int * int * int * W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WArray32.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a32____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t128_0) <@ a32____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a32____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a32____a_ilen_read_bcast_upto8_at (buf:W8.t Array32.t, offset:int,
                                          dELTA:int, lEN:int, tRAIL:int,
                                          cUR:int, aT:int) : int * int *
                                                             int * int *
                                                             W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WArray32.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ __SHLQ_256 (w256, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        (dELTA, lEN, tRAIL, aT, w) <@ a32____a_ilen_read_upto8_at (buf,
        offset, dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc a32____addstate_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array32.t,
                             offset:int, _LEN:int, _TRAILB:int) : W256.t Array7.t *
                                                                  int * int = {
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, r0) <@ a32____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ a32____a_ilen_read_upto32_at (
      buf, offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ a32____a_ilen_read_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ a32____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ a32____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ a32____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ a32____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ a32____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ a32____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ a32____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {
      
    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc a32____absorb_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array32.t,
                           _TRAILB:int, _RATE8:int) : W256.t Array7.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 32;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a32____addstate_avx2 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a32____addstate_avx2 (st, 0, buf, offset,
        _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a32____addstate_avx2 (st, aT, buf, offset, _LEN,
    _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a32____addstate_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                                     buf:W8.t Array32.t, offset:int,
                                     _LEN:int, _TRAILB:int) : W256.t Array25.t *
                                                              int * int = {
    var dELTA:int;
    var aT8:int;
    var w:W256.t;
    var at:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      (dELTA, _LEN, _TRAILB, aT8, w) <@ a32____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, aT, aT8);
      w <- (w `^` st.[(aT %/ 8)]);
      st.[(aT %/ 8)] <- w;
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (32 * (aT %/ 8));
    while ((at < (32 * ((aT %/ 8) + (_LEN %/ 8))))) {
      w <-
      (VPBROADCAST_4u64
      (get64_direct (WArray32.init8 (fun i => buf.[i])) offset));
      offset <- (offset + 8);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
      at <- (at + 32);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, w) <@ a32____a_ilen_read_bcast_upto8_at (
      buf, offset, 0, _LEN, _TRAILB, aT, aT);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc a32____absorb_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                                   buf:W8.t Array32.t, _TRAILB:int,
                                   _RATE8:int) : W256.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 32;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a32____addstate_bcast_avx2x4 (st, aT, buf, 
      offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a32____addstate_bcast_avx2x4 (st, 0, buf,
        offset, _RATE8, 0);
        st <@ _keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a32____addstate_bcast_avx2x4 (st, aT, buf, offset, 
    _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a64____a_ilen_read_upto8_at (buf:W8.t Array64.t, offset:int,
                                    dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                    aT:int) : int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WArray64.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLQ (w, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray64.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          w <@ __SHLQ (w, (aT - cUR));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray64.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ __SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <-
          (zeroextu64
          (get8_direct (WArray64.init8 (fun i => buf.[i])) (offset + dELTA)));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          t8 <@ __SHLQ (t8, (aT - cUR));
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a64____a_ilen_read_upto16_at (buf:W8.t Array64.t, offset:int,
                                     dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                     aT:int) : int * int * int * int * W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray64.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLDQ (w, (aT - cUR));
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a64____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t64_0) <@ a64____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a64____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a64____a_ilen_read_upto32_at (buf:W8.t Array64.t, offset:int,
                                     dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                     aT:int) : int * int * int * int * W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WArray64.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a64____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t128_0) <@ a64____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a64____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a64____a_ilen_read_bcast_upto8_at (buf:W8.t Array64.t, offset:int,
                                          dELTA:int, lEN:int, tRAIL:int,
                                          cUR:int, aT:int) : int * int *
                                                             int * int *
                                                             W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WArray64.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ __SHLQ_256 (w256, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        (dELTA, lEN, tRAIL, aT, w) <@ a64____a_ilen_read_upto8_at (buf,
        offset, dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc a64____a_ilen_write_upto8 (buf:W8.t Array64.t, offset:int, dELTA:int,
                                  lEN:int, w:W64.t) : W8.t Array64.t * int *
                                                      int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (Array64.init
        (WArray64.get8
        (WArray64.set64_direct (WArray64.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (Array64.init
          (WArray64.get8
          (WArray64.set32_direct (WArray64.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu32 w))));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          buf <-
          (Array64.init
          (WArray64.get8
          (WArray64.set16_direct (WArray64.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu16 w))));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          buf <-
          (Array64.init
          (WArray64.get8
          (WArray64.set8_direct (WArray64.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu8 w))));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a64____a_ilen_write_upto16 (buf:W8.t Array64.t, offset:int, dELTA:int,
                                   lEN:int, w:W128.t) : W8.t Array64.t *
                                                        int * int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        buf <-
        (Array64.init
        (WArray64.get8
        (WArray64.set128_direct (WArray64.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          buf <-
          (Array64.init
          (WArray64.get8
          (WArray64.set64_direct (WArray64.init8 (fun i => buf.[i]))
          (offset + dELTA) (MOVV_64 (truncateu64 w)))));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (MOVV_64 (truncateu64 w));
        (buf, dELTA, lEN) <@ a64____a_ilen_write_upto8 (buf, offset, 
        dELTA, lEN, t64);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a64____a_ilen_write_upto32 (buf:W8.t Array64.t, offset:int, dELTA:int,
                                   lEN:int, w:W256.t) : W8.t Array64.t *
                                                        int * int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        buf <-
        (Array64.init
        (WArray64.get8
        (WArray64.set256_direct (WArray64.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          buf <-
          (Array64.init
          (WArray64.get8
          (WArray64.set128_direct (WArray64.init8 (fun i => buf.[i]))
          (offset + dELTA) t128)));
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        (buf, dELTA, lEN) <@ a64____a_ilen_write_upto16 (buf, offset, 
        dELTA, lEN, t128);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a64____a_rlen_write_upto8 (buf:W8.t Array64.t, off:int, data:W64.t,
                                  len:int) : W8.t Array64.t * int = {
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    if ((8 <= len)) {
      buf <-
      (Array64.init
      (WArray64.get8
      (WArray64.set64_direct (WArray64.init8 (fun i => buf.[i])) off data)));
      off <- (off + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        buf <-
        (Array64.init
        (WArray64.get8
        (WArray64.set32_direct (WArray64.init8 (fun i => buf.[i])) off
        (truncateu32 data))));
        off <- (off + 4);
        data <- (data `>>` (W8.of_int 32));
      } else {
        
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        buf <-
        (Array64.init
        (WArray64.get8
        (WArray64.set16_direct (WArray64.init8 (fun i => buf.[i])) off
        (truncateu16 data))));
        off <- (off + 2);
        data <- (data `>>` (W8.of_int 16));
      } else {
        
      }
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        buf <-
        (Array64.init
        (WArray64.get8
        (WArray64.set8_direct (WArray64.init8 (fun i => buf.[i])) off
        (truncateu8 data))));
        off <- (off + 1);
      } else {
        
      }
    }
    return (buf, off);
  }
  proc a64____addstate_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array64.t,
                             offset:int, _LEN:int, _TRAILB:int) : W256.t Array7.t *
                                                                  int * int = {
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, r0) <@ a64____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ a64____a_ilen_read_upto32_at (
      buf, offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ a64____a_ilen_read_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ a64____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ a64____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ a64____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ a64____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ a64____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ a64____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ a64____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {
      
    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc a64____absorb_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array64.t,
                           _TRAILB:int, _RATE8:int) : W256.t Array7.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 64;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a64____addstate_avx2 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a64____addstate_avx2 (st, 0, buf, offset,
        _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a64____addstate_avx2 (st, aT, buf, offset, _LEN,
    _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a64____dumpstate_avx2 (buf:W8.t Array64.t, offset:int, _LEN:int,
                              st:W256.t Array7.t) : W8.t Array64.t * int = {
    var dELTA:int;
    var t128_1:W128.t;
    var t128_0:W128.t;
    var t:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t256_4:W256.t;
    var  _0:int;
    dELTA <- 0;
    if ((8 <= _LEN)) {
      (buf, dELTA,  _0) <@ a64____a_ilen_write_upto32 (buf, offset, dELTA, 8,
      st.[0]);
      _LEN <- (_LEN - 8);
    } else {
      (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto32 (buf, offset, 
      dELTA, _LEN, st.[0]);
    }
    (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto32 (buf, offset, dELTA,
    _LEN, st.[1]);
    if ((0 < _LEN)) {
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t128_0 <- (truncateu128 st.[2]);
      t <- (MOVV_64 (truncateu64 t128_1));
      (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto8 (buf, offset, dELTA,
      _LEN, t);
      t128_1 <- (VPUNPCKH_2u64 t128_1 t128_1);
      if ((0 < _LEN)) {
        t256_0 <-
        (VPBLEND_8u32 st.[3] st.[4]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_1 <-
        (VPBLEND_8u32 st.[4] st.[3]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_2 <-
        (VPBLEND_8u32 st.[5] st.[6]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_3 <-
        (VPBLEND_8u32 st.[6] st.[5]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_4 <-
        (VPBLEND_8u32 t256_0 t256_3
        (W8.of_int
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto32 (buf, offset, 
        dELTA, _LEN, t256_4);
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
          t128_0 <- (VPUNPCKH_2u64 t128_0 t128_0);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_3 t256_1
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_1));
          (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_2 t256_0
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_1 t256_2
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a64____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
      } else {
        
      }
    } else {
      
    }
    offset <- (offset + dELTA);
    return (buf, offset);
  }
  proc a64____addstate_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                                     buf:W8.t Array64.t, offset:int,
                                     _LEN:int, _TRAILB:int) : W256.t Array25.t *
                                                              int * int = {
    var dELTA:int;
    var aT8:int;
    var w:W256.t;
    var at:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      (dELTA, _LEN, _TRAILB, aT8, w) <@ a64____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, aT, aT8);
      w <- (w `^` st.[(aT %/ 8)]);
      st.[(aT %/ 8)] <- w;
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (32 * (aT %/ 8));
    while ((at < (32 * ((aT %/ 8) + (_LEN %/ 8))))) {
      w <-
      (VPBROADCAST_4u64
      (get64_direct (WArray64.init8 (fun i => buf.[i])) offset));
      offset <- (offset + 8);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
      at <- (at + 32);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, w) <@ a64____a_ilen_read_bcast_upto8_at (
      buf, offset, 0, _LEN, _TRAILB, aT, aT);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc a64____absorb_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                                   buf:W8.t Array64.t, _TRAILB:int,
                                   _RATE8:int) : W256.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 64;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a64____addstate_bcast_avx2x4 (st, aT, buf, 
      offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a64____addstate_bcast_avx2x4 (st, 0, buf,
        offset, _RATE8, 0);
        st <@ _keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a64____addstate_bcast_avx2x4 (st, aT, buf, offset, 
    _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a64___dump_updstate_avx2 (buf:W8.t Array64.t, off:int,
                                 st:W64.t Array25.t, at:int, upto:int) : 
  int * int * W8.t Array64.t = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var t256:W256.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf, off2) <@ a64____a_rlen_write_upto8 (buf, off, t64, len);
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 32);
    while ((newat <= upto)) {
      t256 <- (get256_direct (WArray200.init64 (fun i => st.[i])) at);
      buf <-
      (Array64.init
      (WArray64.get8
      (WArray64.set256_direct (WArray64.init8 (fun i => buf.[i])) off t256)));
      at <- newat;
      off <- (off + 32);
      newat <- (newat + 32);
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      buf <-
      (Array64.init
      (WArray64.get8
      (WArray64.set64_direct (WArray64.init8 (fun i => buf.[i])) off t64)));
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      (buf, off) <@ a64____a_rlen_write_upto8 (buf, off, t64,
      (W64.to_uint upto8));
    } else {
      
    }
    at <- upto;
    return (at, off, buf);
  }
  proc a64___squeeze_updstate_avx2 (st:W64.t Array26.t, buf:W8.t Array64.t,
                                    len:int) : W64.t Array26.t *
                                               W8.t Array64.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W8.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ _ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    if ((at = 0)) {
      stk <@ _keccakf1600_st25_avx2 (stk);
      at <- 0;
    } else {
      
    }
    off <- 0;
    len <- (len + at);
    while ((r8 < len)) {
      (at, off, buf) <@ a64___dump_updstate_avx2 (buf, off, stk, at, r8);
      stk <@ _keccakf1600_st25_avx2 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, buf) <@ a64___dump_updstate_avx2 (buf, off, stk, at, len);
    (* Erased call to unspill *)
    st <-
    (Array26.init
    (fun i => (if (0 <= i < (0 + 25)) then stk.[(i - 0)] else st.[i])));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    (truncateu8 (W64.of_int at)))));
    return (st, buf);
  }
  proc a66____a_rlen_read_upto8 (a:W8.t Array66.t, off:int, len:int) : 
  int * W64.t = {
    var w:W64.t;
    var zf:bool;
    var sh:W8.t;
    var x:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    if ((8 <= len)) {
      w <- (get64_direct (WArray66.init8 (fun i => a.[i])) off);
      off <- (off + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        w <-
        (zeroextu64 (get32_direct (WArray66.init8 (fun i => a.[i])) off));
        off <- (off + 4);
        sh <- (W8.of_int 32);
      } else {
        w <- (W64.of_int 0);
        sh <- (W8.of_int 0);
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        x <-
        (zeroextu64 (get16_direct (WArray66.init8 (fun i => a.[i])) off));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        off <- (off + 2);
        sh <- (sh + (W8.of_int 16));
      } else {
        
      }
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        x <-
        (zeroextu64 (get8_direct (WArray66.init8 (fun i => a.[i])) off));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        off <- (off + 1);
      } else {
        
      }
    }
    return (off, w);
  }
  proc a66___add_updstate_avx2 (st:W64.t Array25.t, at:int,
                                buf:W8.t Array66.t, off:int, upto:int) : 
  int * int * W64.t Array25.t = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var r256:W256.t;
    var t256:W256.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      (off2, t64) <@ a66____a_rlen_read_upto8 (buf, off, len);
      len <- (len + at);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 32);
    while ((newat <= upto)) {
      r256 <- (get256_direct (WArray200.init64 (fun i => st.[i])) at);
      t256 <- (get256_direct (WArray66.init8 (fun i => buf.[i])) off);
      r256 <- (r256 `^` t256);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) at r256))
      );
      at <- newat;
      off <- (off + 32);
      newat <- (newat + 32);
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (get64_direct (WArray66.init8 (fun i => buf.[i])) off);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      (off, t64) <@ a66____a_rlen_read_upto8 (buf, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
    } else {
      
    }
    at <- upto;
    return (at, off, st);
  }
  proc a66___update_updstate_avx2 (st:W64.t Array26.t, buf:W8.t Array66.t,
                                   len:int) : W64.t Array26.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W8.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ _ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    off <- 0;
    len <- (len + at);
    while ((r8 <= len)) {
      (at, off, stk) <@ a66___add_updstate_avx2 (stk, at, buf, off, r8);
      stk <@ _keccakf1600_st25_avx2 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (* Erased call to unspill *)
    (at,  _1, stk) <@ a66___add_updstate_avx2 (stk, at, buf, off, len);
    st <-
    (Array26.init
    (fun i => (if (0 <= i < (0 + 25)) then stk.[(i - 0)] else st.[i])));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    (truncateu8 (W64.of_int at)))));
    return st;
  }
  proc a128____a_ilen_read_upto8_at (buf:W8.t Array128.t, offset:int,
                                     dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                     aT:int) : int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WArray128.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLQ (w, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray128.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          w <@ __SHLQ (w, (aT - cUR));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray128.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ __SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <-
          (zeroextu64
          (get8_direct (WArray128.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          t8 <@ __SHLQ (t8, (aT - cUR));
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a128____a_ilen_read_upto16_at (buf:W8.t Array128.t, offset:int,
                                      dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                      aT:int) : int * int * int * int *
                                                W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray128.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLDQ (w, (aT - cUR));
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a128____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t64_0) <@ a128____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a128____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a128____a_ilen_read_upto32_at (buf:W8.t Array128.t, offset:int,
                                      dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                      aT:int) : int * int * int * int *
                                                W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WArray128.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a128____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t128_0) <@ a128____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a128____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a128____a_ilen_read_bcast_upto8_at (buf:W8.t Array128.t, offset:int,
                                           dELTA:int, lEN:int, tRAIL:int,
                                           cUR:int, aT:int) : int * int *
                                                              int * int *
                                                              W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WArray128.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ __SHLQ_256 (w256, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        (dELTA, lEN, tRAIL, aT, w) <@ a128____a_ilen_read_upto8_at (buf,
        offset, dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc a128____a_ilen_write_upto8 (buf:W8.t Array128.t, offset:int,
                                   dELTA:int, lEN:int, w:W64.t) : W8.t Array128.t *
                                                                  int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (Array128.init
        (WArray128.get8
        (WArray128.set64_direct (WArray128.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (Array128.init
          (WArray128.get8
          (WArray128.set32_direct (WArray128.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu32 w))));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          buf <-
          (Array128.init
          (WArray128.get8
          (WArray128.set16_direct (WArray128.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu16 w))));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          buf <-
          (Array128.init
          (WArray128.get8
          (WArray128.set8_direct (WArray128.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu8 w))));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a128____a_ilen_write_upto16 (buf:W8.t Array128.t, offset:int,
                                    dELTA:int, lEN:int, w:W128.t) : W8.t Array128.t *
                                                                    int * int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        buf <-
        (Array128.init
        (WArray128.get8
        (WArray128.set128_direct (WArray128.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          buf <-
          (Array128.init
          (WArray128.get8
          (WArray128.set64_direct (WArray128.init8 (fun i => buf.[i]))
          (offset + dELTA) (MOVV_64 (truncateu64 w)))));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (MOVV_64 (truncateu64 w));
        (buf, dELTA, lEN) <@ a128____a_ilen_write_upto8 (buf, offset, 
        dELTA, lEN, t64);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a128____a_ilen_write_upto32 (buf:W8.t Array128.t, offset:int,
                                    dELTA:int, lEN:int, w:W256.t) : W8.t Array128.t *
                                                                    int * int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        buf <-
        (Array128.init
        (WArray128.get8
        (WArray128.set256_direct (WArray128.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          buf <-
          (Array128.init
          (WArray128.get8
          (WArray128.set128_direct (WArray128.init8 (fun i => buf.[i]))
          (offset + dELTA) t128)));
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        (buf, dELTA, lEN) <@ a128____a_ilen_write_upto16 (buf, offset, 
        dELTA, lEN, t128);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a128____addstate_avx2 (st:W256.t Array7.t, aT:int,
                              buf:W8.t Array128.t, offset:int, _LEN:int,
                              _TRAILB:int) : W256.t Array7.t * int * int = {
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, r0) <@ a128____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ a128____a_ilen_read_upto32_at (
      buf, offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ a128____a_ilen_read_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ a128____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ a128____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ a128____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ a128____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ a128____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ a128____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ a128____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {
      
    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc a128____absorb_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array128.t,
                            _TRAILB:int, _RATE8:int) : W256.t Array7.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 128;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a128____addstate_avx2 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a128____addstate_avx2 (st, 0, buf, offset,
        _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a128____addstate_avx2 (st, aT, buf, offset, _LEN,
    _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a128____dumpstate_avx2 (buf:W8.t Array128.t, offset:int, _LEN:int,
                               st:W256.t Array7.t) : W8.t Array128.t * int = {
    var dELTA:int;
    var t128_1:W128.t;
    var t128_0:W128.t;
    var t:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t256_4:W256.t;
    var  _0:int;
    dELTA <- 0;
    if ((8 <= _LEN)) {
      (buf, dELTA,  _0) <@ a128____a_ilen_write_upto32 (buf, offset, 
      dELTA, 8, st.[0]);
      _LEN <- (_LEN - 8);
    } else {
      (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto32 (buf, offset, 
      dELTA, _LEN, st.[0]);
    }
    (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto32 (buf, offset, dELTA,
    _LEN, st.[1]);
    if ((0 < _LEN)) {
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t128_0 <- (truncateu128 st.[2]);
      t <- (MOVV_64 (truncateu64 t128_1));
      (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto8 (buf, offset, 
      dELTA, _LEN, t);
      t128_1 <- (VPUNPCKH_2u64 t128_1 t128_1);
      if ((0 < _LEN)) {
        t256_0 <-
        (VPBLEND_8u32 st.[3] st.[4]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_1 <-
        (VPBLEND_8u32 st.[4] st.[3]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_2 <-
        (VPBLEND_8u32 st.[5] st.[6]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_3 <-
        (VPBLEND_8u32 st.[6] st.[5]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_4 <-
        (VPBLEND_8u32 t256_0 t256_3
        (W8.of_int
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto32 (buf, offset,
        dELTA, _LEN, t256_4);
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
          t128_0 <- (VPUNPCKH_2u64 t128_0 t128_0);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_3 t256_1
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_1));
          (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_2 t256_0
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_1 t256_2
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a128____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
      } else {
        
      }
    } else {
      
    }
    offset <- (offset + dELTA);
    return (buf, offset);
  }
  proc a136____a_ilen_write_upto8 (buf:W8.t Array136.t, offset:int,
                                   dELTA:int, lEN:int, w:W64.t) : W8.t Array136.t *
                                                                  int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (Array136.init
        (WArray136.get8
        (WArray136.set64_direct (WArray136.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (Array136.init
          (WArray136.get8
          (WArray136.set32_direct (WArray136.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu32 w))));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          buf <-
          (Array136.init
          (WArray136.get8
          (WArray136.set16_direct (WArray136.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu16 w))));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          buf <-
          (Array136.init
          (WArray136.get8
          (WArray136.set8_direct (WArray136.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu8 w))));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a136____a_ilen_write_upto16 (buf:W8.t Array136.t, offset:int,
                                    dELTA:int, lEN:int, w:W128.t) : W8.t Array136.t *
                                                                    int * int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        buf <-
        (Array136.init
        (WArray136.get8
        (WArray136.set128_direct (WArray136.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          buf <-
          (Array136.init
          (WArray136.get8
          (WArray136.set64_direct (WArray136.init8 (fun i => buf.[i]))
          (offset + dELTA) (MOVV_64 (truncateu64 w)))));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (MOVV_64 (truncateu64 w));
        (buf, dELTA, lEN) <@ a136____a_ilen_write_upto8 (buf, offset, 
        dELTA, lEN, t64);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a136____a_ilen_write_upto32 (buf:W8.t Array136.t, offset:int,
                                    dELTA:int, lEN:int, w:W256.t) : W8.t Array136.t *
                                                                    int * int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        buf <-
        (Array136.init
        (WArray136.get8
        (WArray136.set256_direct (WArray136.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          buf <-
          (Array136.init
          (WArray136.get8
          (WArray136.set128_direct (WArray136.init8 (fun i => buf.[i]))
          (offset + dELTA) t128)));
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        (buf, dELTA, lEN) <@ a136____a_ilen_write_upto16 (buf, offset, 
        dELTA, lEN, t128);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a136____dumpstate_avx2 (buf:W8.t Array136.t, offset:int, _LEN:int,
                               st:W256.t Array7.t) : W8.t Array136.t * int = {
    var dELTA:int;
    var t128_1:W128.t;
    var t128_0:W128.t;
    var t:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t256_4:W256.t;
    var  _0:int;
    dELTA <- 0;
    if ((8 <= _LEN)) {
      (buf, dELTA,  _0) <@ a136____a_ilen_write_upto32 (buf, offset, 
      dELTA, 8, st.[0]);
      _LEN <- (_LEN - 8);
    } else {
      (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto32 (buf, offset, 
      dELTA, _LEN, st.[0]);
    }
    (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto32 (buf, offset, dELTA,
    _LEN, st.[1]);
    if ((0 < _LEN)) {
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t128_0 <- (truncateu128 st.[2]);
      t <- (MOVV_64 (truncateu64 t128_1));
      (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto8 (buf, offset, 
      dELTA, _LEN, t);
      t128_1 <- (VPUNPCKH_2u64 t128_1 t128_1);
      if ((0 < _LEN)) {
        t256_0 <-
        (VPBLEND_8u32 st.[3] st.[4]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_1 <-
        (VPBLEND_8u32 st.[4] st.[3]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_2 <-
        (VPBLEND_8u32 st.[5] st.[6]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_3 <-
        (VPBLEND_8u32 st.[6] st.[5]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_4 <-
        (VPBLEND_8u32 t256_0 t256_3
        (W8.of_int
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto32 (buf, offset,
        dELTA, _LEN, t256_4);
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
          t128_0 <- (VPUNPCKH_2u64 t128_0 t128_0);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_3 t256_1
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_1));
          (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_2 t256_0
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto8 (buf, offset,
          dELTA, _LEN, t);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_1 t256_2
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a136____a_ilen_write_upto32 (buf, offset,
          dELTA, _LEN, t256_4);
        } else {
          
        }
      } else {
        
      }
    } else {
      
    }
    offset <- (offset + dELTA);
    return (buf, offset);
  }
  proc a136____dumpstate_avx2x4 (buf0:W8.t Array136.t, buf1:W8.t Array136.t,
                                 buf2:W8.t Array136.t, buf3:W8.t Array136.t,
                                 offset:int, _LEN:int, st:W256.t Array25.t) : 
  W8.t Array136.t * W8.t Array136.t * W8.t Array136.t * W8.t Array136.t * int = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    var  _6:int;
    var  _7:int;
    i <- 0;
    while ((i < (32 * (_LEN %/ 32)))) {
      x0 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 32)));
      x1 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 32)));
      x2 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 32)));
      x3 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 32)));
      i <- (i + 32);
      (x0, x1, x2, x3) <@ __4u64x4_u256x4 (x0, x1, x2, x3);
      buf0 <-
      (Array136.init
      (WArray136.get8
      (WArray136.set256_direct (WArray136.init8 (fun i_0 => buf0.[i_0]))
      offset x0)));
      buf1 <-
      (Array136.init
      (WArray136.get8
      (WArray136.set256_direct (WArray136.init8 (fun i_0 => buf1.[i_0]))
      offset x1)));
      buf2 <-
      (Array136.init
      (WArray136.get8
      (WArray136.set256_direct (WArray136.init8 (fun i_0 => buf2.[i_0]))
      offset x2)));
      buf3 <-
      (Array136.init
      (WArray136.get8
      (WArray136.set256_direct (WArray136.init8 (fun i_0 => buf3.[i_0]))
      offset x3)));
      offset <- (offset + 32);
    }
    while ((i < (8 * (_LEN %/ 8)))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      buf0 <-
      (Array136.init
      (WArray136.get8
      (WArray136.set64_direct (WArray136.init8 (fun i_0 => buf0.[i_0]))
      offset t0)));
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      buf1 <-
      (Array136.init
      (WArray136.get8
      (WArray136.set64_direct (WArray136.init8 (fun i_0 => buf1.[i_0]))
      offset t1)));
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      buf2 <-
      (Array136.init
      (WArray136.get8
      (WArray136.set64_direct (WArray136.init8 (fun i_0 => buf2.[i_0]))
      offset t2)));
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      buf3 <-
      (Array136.init
      (WArray136.get8
      (WArray136.set64_direct (WArray136.init8 (fun i_0 => buf3.[i_0]))
      offset t3)));
      i <- (i + 8);
      offset <- (offset + 8);
    }
    if ((0 < (_LEN %% 8))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      (buf0,  _0,  _1) <@ a136____a_ilen_write_upto8 (buf0, offset, 0,
      (_LEN %% 8), t0);
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      (buf1,  _2,  _3) <@ a136____a_ilen_write_upto8 (buf1, offset, 0,
      (_LEN %% 8), t1);
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      (buf2,  _4,  _5) <@ a136____a_ilen_write_upto8 (buf2, offset, 0,
      (_LEN %% 8), t2);
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      (buf3,  _6,  _7) <@ a136____a_ilen_write_upto8 (buf3, offset, 0,
      (_LEN %% 8), t3);
      offset <- (offset + (_LEN %% 8));
    } else {
      
    }
    return (buf0, buf1, buf2, buf3, offset);
  }
  proc a168____a_ilen_write_upto8 (buf:W8.t Array168.t, offset:int,
                                   dELTA:int, lEN:int, w:W64.t) : W8.t Array168.t *
                                                                  int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (Array168.init
        (WArray168.get8
        (WArray168.set64_direct (WArray168.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (Array168.init
          (WArray168.get8
          (WArray168.set32_direct (WArray168.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu32 w))));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          buf <-
          (Array168.init
          (WArray168.get8
          (WArray168.set16_direct (WArray168.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu16 w))));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          buf <-
          (Array168.init
          (WArray168.get8
          (WArray168.set8_direct (WArray168.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu8 w))));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a168____dumpstate_avx2x4 (buf0:W8.t Array168.t, buf1:W8.t Array168.t,
                                 buf2:W8.t Array168.t, buf3:W8.t Array168.t,
                                 offset:int, _LEN:int, st:W256.t Array25.t) : 
  W8.t Array168.t * W8.t Array168.t * W8.t Array168.t * W8.t Array168.t * int = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    var  _6:int;
    var  _7:int;
    i <- 0;
    while ((i < (32 * (_LEN %/ 32)))) {
      x0 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 32)));
      x1 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 32)));
      x2 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 32)));
      x3 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 32)));
      i <- (i + 32);
      (x0, x1, x2, x3) <@ __4u64x4_u256x4 (x0, x1, x2, x3);
      buf0 <-
      (Array168.init
      (WArray168.get8
      (WArray168.set256_direct (WArray168.init8 (fun i_0 => buf0.[i_0]))
      offset x0)));
      buf1 <-
      (Array168.init
      (WArray168.get8
      (WArray168.set256_direct (WArray168.init8 (fun i_0 => buf1.[i_0]))
      offset x1)));
      buf2 <-
      (Array168.init
      (WArray168.get8
      (WArray168.set256_direct (WArray168.init8 (fun i_0 => buf2.[i_0]))
      offset x2)));
      buf3 <-
      (Array168.init
      (WArray168.get8
      (WArray168.set256_direct (WArray168.init8 (fun i_0 => buf3.[i_0]))
      offset x3)));
      offset <- (offset + 32);
    }
    while ((i < (8 * (_LEN %/ 8)))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      buf0 <-
      (Array168.init
      (WArray168.get8
      (WArray168.set64_direct (WArray168.init8 (fun i_0 => buf0.[i_0]))
      offset t0)));
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      buf1 <-
      (Array168.init
      (WArray168.get8
      (WArray168.set64_direct (WArray168.init8 (fun i_0 => buf1.[i_0]))
      offset t1)));
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      buf2 <-
      (Array168.init
      (WArray168.get8
      (WArray168.set64_direct (WArray168.init8 (fun i_0 => buf2.[i_0]))
      offset t2)));
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      buf3 <-
      (Array168.init
      (WArray168.get8
      (WArray168.set64_direct (WArray168.init8 (fun i_0 => buf3.[i_0]))
      offset t3)));
      i <- (i + 8);
      offset <- (offset + 8);
    }
    if ((0 < (_LEN %% 8))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      (buf0,  _0,  _1) <@ a168____a_ilen_write_upto8 (buf0, offset, 0,
      (_LEN %% 8), t0);
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      (buf1,  _2,  _3) <@ a168____a_ilen_write_upto8 (buf1, offset, 0,
      (_LEN %% 8), t1);
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      (buf2,  _4,  _5) <@ a168____a_ilen_write_upto8 (buf2, offset, 0,
      (_LEN %% 8), t2);
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      (buf3,  _6,  _7) <@ a168____a_ilen_write_upto8 (buf3, offset, 0,
      (_LEN %% 8), t3);
      offset <- (offset + (_LEN %% 8));
    } else {
      
    }
    return (buf0, buf1, buf2, buf3, offset);
  }
  proc a_COMMITMENT_HASH____a_ilen_read_upto8_at (buf:W8.t Array48.t,
                                                  offset:int, dELTA:int,
                                                  lEN:int, tRAIL:int,
                                                  cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WArray48.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLQ (w, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray48.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          w <@ __SHLQ (w, (aT - cUR));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray48.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ __SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <-
          (zeroextu64
          (get8_direct (WArray48.init8 (fun i => buf.[i])) (offset + dELTA)));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          t8 <@ __SHLQ (t8, (aT - cUR));
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_COMMITMENT_HASH____a_ilen_read_upto16_at (buf:W8.t Array48.t,
                                                   offset:int, dELTA:int,
                                                   lEN:int, tRAIL:int,
                                                   cUR:int, aT:int) : 
  int * int * int * int * W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray48.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLDQ (w, (aT - cUR));
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a_COMMITMENT_HASH____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t64_0) <@ a_COMMITMENT_HASH____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a_COMMITMENT_HASH____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_COMMITMENT_HASH____a_ilen_read_upto32_at (buf:W8.t Array48.t,
                                                   offset:int, dELTA:int,
                                                   lEN:int, tRAIL:int,
                                                   cUR:int, aT:int) : 
  int * int * int * int * W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WArray48.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a_COMMITMENT_HASH____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t128_0) <@ a_COMMITMENT_HASH____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a_COMMITMENT_HASH____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_COMMITMENT_HASH____a_ilen_read_bcast_upto8_at (buf:W8.t Array48.t,
                                                        offset:int,
                                                        dELTA:int, lEN:int,
                                                        tRAIL:int, cUR:int,
                                                        aT:int) : int * int *
                                                                  int * int *
                                                                  W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WArray48.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ __SHLQ_256 (w256, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        (dELTA, lEN, tRAIL, aT, w) <@ a_COMMITMENT_HASH____a_ilen_read_upto8_at (
        buf, offset, dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc a_COMMITMENT_HASH____a_ilen_write_upto8 (buf:W8.t Array48.t,
                                                offset:int, dELTA:int,
                                                lEN:int, w:W64.t) : W8.t Array48.t *
                                                                    int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (Array48.init
        (WArray48.get8
        (WArray48.set64_direct (WArray48.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (Array48.init
          (WArray48.get8
          (WArray48.set32_direct (WArray48.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu32 w))));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          buf <-
          (Array48.init
          (WArray48.get8
          (WArray48.set16_direct (WArray48.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu16 w))));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          buf <-
          (Array48.init
          (WArray48.get8
          (WArray48.set8_direct (WArray48.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu8 w))));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a_COMMITMENT_HASH____a_ilen_write_upto16 (buf:W8.t Array48.t,
                                                 offset:int, dELTA:int,
                                                 lEN:int, w:W128.t) : 
  W8.t Array48.t * int * int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        buf <-
        (Array48.init
        (WArray48.get8
        (WArray48.set128_direct (WArray48.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          buf <-
          (Array48.init
          (WArray48.get8
          (WArray48.set64_direct (WArray48.init8 (fun i => buf.[i]))
          (offset + dELTA) (MOVV_64 (truncateu64 w)))));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (MOVV_64 (truncateu64 w));
        (buf, dELTA, lEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto8 (
        buf, offset, dELTA, lEN, t64);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a_COMMITMENT_HASH____a_ilen_write_upto32 (buf:W8.t Array48.t,
                                                 offset:int, dELTA:int,
                                                 lEN:int, w:W256.t) : 
  W8.t Array48.t * int * int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        buf <-
        (Array48.init
        (WArray48.get8
        (WArray48.set256_direct (WArray48.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          buf <-
          (Array48.init
          (WArray48.get8
          (WArray48.set128_direct (WArray48.init8 (fun i => buf.[i]))
          (offset + dELTA) t128)));
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        (buf, dELTA, lEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto16 (
        buf, offset, dELTA, lEN, t128);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc a_COMMITMENT_HASH____addstate_avx2 (st:W256.t Array7.t, aT:int,
                                           buf:W8.t Array48.t, offset:int,
                                           _LEN:int, _TRAILB:int) : W256.t Array7.t *
                                                                    int * int = {
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, r0) <@ a_COMMITMENT_HASH____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ a_COMMITMENT_HASH____a_ilen_read_upto32_at (
      buf, offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ a_COMMITMENT_HASH____a_ilen_read_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ a_COMMITMENT_HASH____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ a_COMMITMENT_HASH____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ a_COMMITMENT_HASH____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ a_COMMITMENT_HASH____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ a_COMMITMENT_HASH____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ a_COMMITMENT_HASH____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ a_COMMITMENT_HASH____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {
      
    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc a_COMMITMENT_HASH____absorb_avx2 (st:W256.t Array7.t, aT:int,
                                         buf:W8.t Array48.t, _TRAILB:int,
                                         _RATE8:int) : W256.t Array7.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 48;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a_COMMITMENT_HASH____addstate_avx2 (st, aT, 
      buf, offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a_COMMITMENT_HASH____addstate_avx2 (st, 0, 
        buf, offset, _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a_COMMITMENT_HASH____addstate_avx2 (st, aT, buf, 
    offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a_COMMITMENT_HASH____dumpstate_avx2 (buf:W8.t Array48.t, offset:int,
                                            _LEN:int, st:W256.t Array7.t) : 
  W8.t Array48.t * int = {
    var dELTA:int;
    var t128_1:W128.t;
    var t128_0:W128.t;
    var t:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t256_4:W256.t;
    var  _0:int;
    dELTA <- 0;
    if ((8 <= _LEN)) {
      (buf, dELTA,  _0) <@ a_COMMITMENT_HASH____a_ilen_write_upto32 (
      buf, offset, dELTA, 8, st.[0]);
      _LEN <- (_LEN - 8);
    } else {
      (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto32 (
      buf, offset, dELTA, _LEN, st.[0]);
    }
    (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto32 (buf,
    offset, dELTA, _LEN, st.[1]);
    if ((0 < _LEN)) {
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t128_0 <- (truncateu128 st.[2]);
      t <- (MOVV_64 (truncateu64 t128_1));
      (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto8 (
      buf, offset, dELTA, _LEN, t);
      t128_1 <- (VPUNPCKH_2u64 t128_1 t128_1);
      if ((0 < _LEN)) {
        t256_0 <-
        (VPBLEND_8u32 st.[3] st.[4]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_1 <-
        (VPBLEND_8u32 st.[4] st.[3]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_2 <-
        (VPBLEND_8u32 st.[5] st.[6]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_3 <-
        (VPBLEND_8u32 st.[6] st.[5]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_4 <-
        (VPBLEND_8u32 t256_0 t256_3
        (W8.of_int
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto32 (
        buf, offset, dELTA, _LEN, t256_4);
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto8 (
          buf, offset, dELTA, _LEN, t);
          t128_0 <- (VPUNPCKH_2u64 t128_0 t128_0);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_3 t256_1
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto32 (
          buf, offset, dELTA, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_1));
          (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto8 (
          buf, offset, dELTA, _LEN, t);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_2 t256_0
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto32 (
          buf, offset, dELTA, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto8 (
          buf, offset, dELTA, _LEN, t);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_1 t256_2
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ a_COMMITMENT_HASH____a_ilen_write_upto32 (
          buf, offset, dELTA, _LEN, t256_4);
        } else {
          
        }
      } else {
        
      }
    } else {
      
    }
    offset <- (offset + dELTA);
    return (buf, offset);
  }
  proc a_VERIFICATION_KEY____a_ilen_read_upto8_at (buf:W8.t Array1952.t,
                                                   offset:int, dELTA:int,
                                                   lEN:int, tRAIL:int,
                                                   cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WArray1952.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLQ (w, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray1952.init8 (fun i => buf.[i]))
          (offset + dELTA)));
          w <@ __SHLQ (w, (aT - cUR));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray1952.init8 (fun i => buf.[i]))
          (offset + dELTA)));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ __SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <-
          (zeroextu64
          (get8_direct (WArray1952.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          t8 <@ __SHLQ (t8, (aT - cUR));
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_VERIFICATION_KEY____a_ilen_read_upto16_at (buf:W8.t Array1952.t,
                                                    offset:int, dELTA:int,
                                                    lEN:int, tRAIL:int,
                                                    cUR:int, aT:int) : 
  int * int * int * int * W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray1952.init8 (fun i => buf.[i])) (offset + dELTA)
        );
        w <@ __SHLDQ (w, (aT - cUR));
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a_VERIFICATION_KEY____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t64_0) <@ a_VERIFICATION_KEY____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a_VERIFICATION_KEY____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_VERIFICATION_KEY____a_ilen_read_upto32_at (buf:W8.t Array1952.t,
                                                    offset:int, dELTA:int,
                                                    lEN:int, tRAIL:int,
                                                    cUR:int, aT:int) : 
  int * int * int * int * W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WArray1952.init8 (fun i => buf.[i])) (offset + dELTA)
        );
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a_VERIFICATION_KEY____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t128_0) <@ a_VERIFICATION_KEY____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a_VERIFICATION_KEY____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_VERIFICATION_KEY____a_ilen_read_bcast_upto8_at (buf:W8.t Array1952.t,
                                                         offset:int,
                                                         dELTA:int, lEN:int,
                                                         tRAIL:int, cUR:int,
                                                         aT:int) : int *
                                                                   int *
                                                                   int *
                                                                   int *
                                                                   W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WArray1952.init8 (fun i => buf.[i])) (offset + dELTA))
        );
        w256 <@ __SHLQ_256 (w256, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        (dELTA, lEN, tRAIL, aT, w) <@ a_VERIFICATION_KEY____a_ilen_read_upto8_at (
        buf, offset, dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc a_VERIFICATION_KEY____addstate_avx2 (st:W256.t Array7.t, aT:int,
                                            buf:W8.t Array1952.t, offset:int,
                                            _LEN:int, _TRAILB:int) : 
  W256.t Array7.t * int * int = {
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, r0) <@ a_VERIFICATION_KEY____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ a_VERIFICATION_KEY____a_ilen_read_upto32_at (
      buf, offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ a_VERIFICATION_KEY____a_ilen_read_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ a_VERIFICATION_KEY____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ a_VERIFICATION_KEY____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ a_VERIFICATION_KEY____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ a_VERIFICATION_KEY____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ a_VERIFICATION_KEY____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ a_VERIFICATION_KEY____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ a_VERIFICATION_KEY____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {
      
    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc a_VERIFICATION_KEY____absorb_avx2 (st:W256.t Array7.t, aT:int,
                                          buf:W8.t Array1952.t, _TRAILB:int,
                                          _RATE8:int) : W256.t Array7.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- (32 + (6 * (((23 - 13) * 256) %/ 8)));
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a_VERIFICATION_KEY____addstate_avx2 (st, aT, 
      buf, offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a_VERIFICATION_KEY____addstate_avx2 (st, 0, 
        buf, offset, _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a_VERIFICATION_KEY____addstate_avx2 (st, aT, buf,
    offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (buf:W8.t Array768.t,
                                                     offset:int, dELTA:int,
                                                     lEN:int, tRAIL:int,
                                                     cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WArray768.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLQ (w, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray768.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          w <@ __SHLQ (w, (aT - cUR));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray768.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ __SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <-
          (zeroextu64
          (get8_direct (WArray768.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          t8 <@ __SHLQ (t8, (aT - cUR));
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_ENCODED_COMMITMENT____a_ilen_read_upto16_at (buf:W8.t Array768.t,
                                                      offset:int, dELTA:int,
                                                      lEN:int, tRAIL:int,
                                                      cUR:int, aT:int) : 
  int * int * int * int * W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray768.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ __SHLDQ (w, (aT - cUR));
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t64_0) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_ENCODED_COMMITMENT____a_ilen_read_upto32_at (buf:W8.t Array768.t,
                                                      offset:int, dELTA:int,
                                                      lEN:int, tRAIL:int,
                                                      cUR:int, aT:int) : 
  int * int * int * int * W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WArray768.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t128_0) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc a_ENCODED_COMMITMENT____a_ilen_read_bcast_upto8_at (buf:W8.t Array768.t,
                                                           offset:int,
                                                           dELTA:int,
                                                           lEN:int,
                                                           tRAIL:int,
                                                           cUR:int, aT:int) : 
  int * int * int * int * W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WArray768.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ __SHLQ_256 (w256, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        (dELTA, lEN, tRAIL, aT, w) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (
        buf, offset, dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc a_ENCODED_COMMITMENT____addstate_avx2 (st:W256.t Array7.t, aT:int,
                                              buf:W8.t Array768.t,
                                              offset:int, _LEN:int,
                                              _TRAILB:int) : W256.t Array7.t *
                                                             int * int = {
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, r0) <@ a_ENCODED_COMMITMENT____a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto32_at (
      buf, offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ a_ENCODED_COMMITMENT____a_ilen_read_upto32_at (
        buf, offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {
      
    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc a_ENCODED_COMMITMENT____absorb_avx2 (st:W256.t Array7.t, aT:int,
                                            buf:W8.t Array768.t, _TRAILB:int,
                                            _RATE8:int) : W256.t Array7.t *
                                                          int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- (((4 * 256) %/ 8) * 6);
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ a_ENCODED_COMMITMENT____addstate_avx2 (st, 
      aT, buf, offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ a_ENCODED_COMMITMENT____addstate_avx2 (st, 0,
        buf, offset, _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ a_ENCODED_COMMITMENT____addstate_avx2 (st, aT, buf,
    offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc shake256_init_state () : W256.t Array7.t = {
    var state:W256.t Array7.t;
    state <- witness;
    state <@ __state_init_avx2 ();
    return state;
  }
  proc shake256_permute (state:W256.t Array7.t) : W256.t Array7.t = {
    
    state <@ _keccakf1600_avx2 (state);
    return state;
  }
  proc squeeze_128_bytes (array:W8.t Array128.t, state:W256.t Array7.t) : 
  W8.t Array128.t = {
    var offset:int;
    var  _0:int;
    offset <- 0;
    (array,  _0) <@ a128____dumpstate_avx2 (array, offset, 128, state);
    return array;
  }
  proc shake256_absorb_34 (seed:W8.t Array32.t, extra:W8.t Array2.t) : 
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    var  _1:int;
    state <- witness;
    state <@ shake256_init_state ();
    (state,  _0) <@ a32____absorb_avx2 (state, 0, seed, 0, 136);
    (state,  _1) <@ a2____absorb_avx2 (state, 32, extra, 31, 136);
    state <@ shake256_permute (state);
    return state;
  }
  proc shake256_absorb_66 (rho_prime:W8.t Array64.t, domain_separator:W16.t) : 
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var ds:W8.t Array2.t;
    var  _0:int;
    var  _1:int;
    ds <- witness;
    state <- witness;
    state <@ shake256_init_state ();
    (state,  _0) <@ a64____absorb_avx2 (state, 0, rho_prime, 0, 136);
    ds <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => ds.[i])) 0 domain_separator)));
    (state,  _1) <@ a2____absorb_avx2 (state, 64, ds, 31, 136);
    state <@ shake256_permute (state);
    return state;
  }
  proc shake256_absorb_128 (block:W8.t Array128.t) : W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ shake256_init_state ();
    (state,  _0) <@ a128____absorb_avx2 (state, 0, block, 31, 136);
    state <@ shake256_permute (state);
    return state;
  }
  proc shake256_absorb_commitment_hash (hash:W8.t Array48.t) : W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ shake256_init_state ();
    (state,  _0) <@ a_COMMITMENT_HASH____absorb_avx2 (state, 0, hash, 31,
    136);
    state <@ shake256_permute (state);
    return state;
  }
  proc shake256_squeeze_block (block:W8.t Array136.t, state:W256.t Array7.t) : 
  W8.t Array136.t = {
    var offset:int;
    var  _0:int;
    offset <- 0;
    (block,  _0) <@ a136____dumpstate_avx2 (block, offset, 136, state);
    return block;
  }
  proc squeeze_64_bytes (array:W8.t Array64.t, state:W256.t Array7.t) : 
  W8.t Array64.t = {
    var offset:int;
    var  _0:int;
    offset <- 0;
    (array,  _0) <@ a64____dumpstate_avx2 (array, offset, 64, state);
    return array;
  }
  proc squeeze_commitment_hash_bytes (array:W8.t Array48.t,
                                      state:W256.t Array7.t) : W8.t Array48.t = {
    var offset:int;
    var  _0:int;
    offset <- 0;
    (array,  _0) <@ a_COMMITMENT_HASH____dumpstate_avx2 (array, offset, 48,
    state);
    return array;
  }
  proc __derive_message_representative (verification_key_hash:W8.t Array64.t,
                                        context_pointer:int,
                                        context_size:int,
                                        message_pointer:int, message_size:int) : 
  W8.t Array64.t = {
    var message_representative:W8.t Array64.t;
    var copied_32_bytes:W256.t;
    var prefix:W8.t Array66.t;
    var trailb:W8.t;
    var state:W64.t Array26.t;
    var rate64:int;
    var len:int;
    var buf:int;
    message_representative <- witness;
    prefix <- witness;
    state <- witness;
    copied_32_bytes <-
    (get256_direct (WArray64.init8 (fun i => verification_key_hash.[i])) 0);
    prefix <-
    (Array66.init
    (WArray66.get8
    (WArray66.set256_direct (WArray66.init8 (fun i => prefix.[i])) 0
    copied_32_bytes)));
    copied_32_bytes <-
    (get256_direct (WArray64.init8 (fun i => verification_key_hash.[i])) 32);
    prefix <-
    (Array66.init
    (WArray66.get8
    (WArray66.set256_direct (WArray66.init8 (fun i => prefix.[i])) 32
    copied_32_bytes)));
    prefix.[64] <- (W8.of_int 0);
    prefix.[65] <- (truncateu8 (W64.of_int context_size));
    (* Erased call to spill *)
    rate64 <- 17;
    trailb <- (W8.of_int 31);
    state <@ _init_updstate_avx2 (state, rate64, trailb);
    len <- 66;
    state <@ a66___update_updstate_avx2 (state, prefix, len);
    (* Erased call to unspill *)
    buf <- context_pointer;
    len <- context_size;
    state <@ _absorb_m_updstate_avx2 (state, buf, len);
    (* Erased call to unspill *)
    buf <- message_pointer;
    len <- message_size;
    state <@ _absorb_m_updstate_avx2 (state, buf, len);
    state <@ _finish_updstate_avx2 (state);
    len <- 64;
    (state, message_representative) <@ a64___squeeze_updstate_avx2 (state,
    message_representative, len);
    return message_representative;
  }
  proc hash_verification_key (verification_key_hash:W8.t Array64.t,
                              verification_key:W8.t Array1952.t) : W8.t Array64.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ shake256_init_state ();
    (state,  _0) <@ a_VERIFICATION_KEY____absorb_avx2 (state, 0,
    verification_key, 31, 136);
    state <@ shake256_permute (state);
    verification_key_hash <@ squeeze_64_bytes (verification_key_hash, state);
    return verification_key_hash;
  }
  proc __derive_commitment_hash (message_representative:W8.t Array64.t,
                                 encoded_commitment:W8.t Array768.t) : 
  W8.t Array48.t = {
    var commitment_hash:W8.t Array48.t;
    var state:W256.t Array7.t;
    var  _0:int;
    var  _1:int;
    commitment_hash <- witness;
    state <- witness;
    state <@ shake256_init_state ();
    (state,  _0) <@ a64____absorb_avx2 (state, 0, message_representative, 0,
    136);
    (state,  _1) <@ a_ENCODED_COMMITMENT____absorb_avx2 (state, 64,
    encoded_commitment, 31, 136);
    state <@ shake256_permute (state);
    commitment_hash <@ squeeze_commitment_hash_bytes (commitment_hash,
    state);
    return commitment_hash;
  }
  proc shake128_absorb_34_4x (state:W256.t Array25.t, rho:W8.t Array32.t,
                              domain_separators:W16.t Array4.t) : W256.t Array25.t = {
    var d0:W8.t Array2.t;
    var d1:W8.t Array2.t;
    var d2:W8.t Array2.t;
    var d3:W8.t Array2.t;
    var  _0:int;
    var  _1:int;
    d0 <- witness;
    d1 <- witness;
    d2 <- witness;
    d3 <- witness;
    state <@ __state_init_avx2x4 (state);
    (state,  _0) <@ a32____absorb_bcast_avx2x4 (state, 0, rho, 0, 168);
    d0 <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => d0.[i])) 0 domain_separators.[0])
    ));
    d1 <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => d1.[i])) 0 domain_separators.[1])
    ));
    d2 <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => d2.[i])) 0 domain_separators.[2])
    ));
    d3 <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => d3.[i])) 0 domain_separators.[3])
    ));
    (state,  _1) <@ a2____absorb_avx2x4 (state, 32, d0, d1, d2, d3, 31, 168);
    return state;
  }
  proc shake256_absorb_66_4x (state:W256.t Array25.t,
                              rho_prime:W8.t Array64.t,
                              starting_domain_separator:W16.t) : W256.t Array25.t = {
    var t:W16.t;
    var d0:W8.t Array2.t;
    var d1:W8.t Array2.t;
    var d2:W8.t Array2.t;
    var d3:W8.t Array2.t;
    var  _0:int;
    var  _1:int;
    d0 <- witness;
    d1 <- witness;
    d2 <- witness;
    d3 <- witness;
    state <@ __state_init_avx2x4 (state);
    (state,  _0) <@ a64____absorb_bcast_avx2x4 (state, 0, rho_prime, 0, 136);
    t <- starting_domain_separator;
    d0 <-
    (Array2.init
    (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => d0.[i])) 0 t)));
    t <- (t + (W16.of_int 1));
    d1 <-
    (Array2.init
    (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => d1.[i])) 0 t)));
    t <- (t + (W16.of_int 1));
    d2 <-
    (Array2.init
    (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => d2.[i])) 0 t)));
    t <- (t + (W16.of_int 1));
    d3 <-
    (Array2.init
    (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => d3.[i])) 0 t)));
    (state,  _1) <@ a2____absorb_avx2x4 (state, 64, d0, d1, d2, d3, 31, 136);
    return state;
  }
  proc shake128_squeezeblock4x (state:W256.t Array25.t, h0:W8.t Array168.t,
                                h1:W8.t Array168.t, h2:W8.t Array168.t,
                                h3:W8.t Array168.t) : W256.t Array25.t *
                                                      W8.t Array168.t *
                                                      W8.t Array168.t *
                                                      W8.t Array168.t *
                                                      W8.t Array168.t = {
    var offset:int;
    var  _0:int;
    state <@ _keccakf1600_avx2x4 (state);
    offset <- 0;
    (h0, h1, h2, h3,  _0) <@ a168____dumpstate_avx2x4 (h0, h1, h2, h3,
    offset, 168, state);
    return (state, h0, h1, h2, h3);
  }
  proc shake256_squeezeblock4x (state:W256.t Array25.t, h0:W8.t Array136.t,
                                h1:W8.t Array136.t, h2:W8.t Array136.t,
                                h3:W8.t Array136.t) : W256.t Array25.t *
                                                      W8.t Array136.t *
                                                      W8.t Array136.t *
                                                      W8.t Array136.t *
                                                      W8.t Array136.t = {
    var offset:int;
    var  _0:int;
    state <@ _keccakf1600_avx2x4 (state);
    offset <- 0;
    (h0, h1, h2, h3,  _0) <@ a136____dumpstate_avx2x4 (h0, h1, h2, h3,
    offset, 136, state);
    return (state, h0, h1, h2, h3);
  }
  proc matrix_A____bytestream_to_potential_coefficients (bytestream:W256.t) : 
  W256.t = {
    var coefficients:W256.t;
    var constants:W256.t;
    constants <- matrix_A__DECODING_TABLE.[0];
    coefficients <- (VPERMD constants bytestream);
    constants <- matrix_A__DECODING_TABLE.[1];
    coefficients <- (VPSHUFB_256 coefficients constants);
    constants <- matrix_A__DECODING_TABLE.[2];
    coefficients <- (VPAND_256 coefficients constants);
    return coefficients;
  }
  proc matrix_A__rejection_sample_multiple_blocks (polynomial:W32.t Array256.t,
                                                   randombytes:W8.t Array848.t) : 
  W32.t Array256.t * W64.t = {
    var filled:W64.t;
    var shuffle_table_pointer:W8.t Array256.t;
    var bytes_filled:W64.t;
    var input_offset:W64.t;
    var modulus:W256.t;
    var stop_sampling:W64.t;
    var potential_coefficients:W256.t;
    var compare_with_field_modulus:W256.t;
    var good:W64.t;
    var lower_coefficients:W128.t;
    var good_lower:W64.t;
    var shuffle_table_idx:W64.t;
    var shuffles:W128.t;
    var upper_coefficients:W128.t;
    var good_upper:W64.t;
    var byte0:W32.t;
    var byte1:W32.t;
    var byte2:W32.t;
    var coeff:W32.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    shuffle_table_pointer <- witness;
    shuffle_table_pointer <- matrix_A__SHUFFLE_TABLE;
    bytes_filled <- (W64.of_int 0);
    input_offset <- (W64.of_int 0);
    modulus <- mODULUS_VECTOR;
    stop_sampling <- (W64.of_int 0);
    while ((stop_sampling <> (W64.of_int 1))) {
      potential_coefficients <-
      (get256_direct (WArray848.init8 (fun i => randombytes.[i]))
      (W64.to_uint input_offset));
      potential_coefficients <@ matrix_A____bytestream_to_potential_coefficients (
      potential_coefficients);
      input_offset <- (input_offset + (W64.of_int 24));
      compare_with_field_modulus <-
      (VPCMPGT_8u32 modulus potential_coefficients);
      good <- (zeroextu64 (MOVEMASK_8u32 compare_with_field_modulus));
      lower_coefficients <-
      (VEXTRACTI128 potential_coefficients (W8.of_int 0));
      good_lower <- good;
      good_lower <- (good_lower `&` (W64.of_int 15));
      shuffle_table_idx <- good_lower;
      shuffle_table_idx <- (shuffle_table_idx `<<` (W8.of_int 4));
      shuffles <-
      (get128_direct (WArray256.init8 (fun i => shuffle_table_pointer.[i]))
      (W64.to_uint shuffle_table_idx));
      lower_coefficients <- (VPSHUFB_128 lower_coefficients shuffles);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set128_direct (WArray1024.init32 (fun i => polynomial.[i]))
      (W64.to_uint bytes_filled) lower_coefficients)));
      ( _0,  _1,  _2,  _3,  _4, good_lower) <- (POPCNT_64 good_lower);
      good_lower <- (good_lower `<<` (W8.of_int 2));
      bytes_filled <- (bytes_filled + good_lower);
      upper_coefficients <-
      (VEXTRACTI128 potential_coefficients (W8.of_int 1));
      good_upper <- good;
      good_upper <- (good_upper `>>` (W8.of_int 4));
      shuffle_table_idx <- good_upper;
      shuffle_table_idx <- (shuffle_table_idx `<<` (W8.of_int 4));
      shuffles <-
      (get128_direct (WArray256.init8 (fun i => shuffle_table_pointer.[i]))
      (W64.to_uint shuffle_table_idx));
      upper_coefficients <- (VPSHUFB_128 upper_coefficients shuffles);
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set128_direct (WArray1024.init32 (fun i => polynomial.[i]))
      (W64.to_uint bytes_filled) upper_coefficients)));
      ( _5,  _6,  _7,  _8,  _9, good_upper) <- (POPCNT_64 good_upper);
      good_upper <- (good_upper `<<` (W8.of_int 2));
      bytes_filled <- (bytes_filled + good_upper);
      stop_sampling <- (W64.of_int 0);
      if (((W64.of_int (((256 * 32) %/ 8) - 32)) \ule bytes_filled)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int (5 * 168)) \ule input_offset)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    filled <- bytes_filled;
    filled <- (filled `>>` (W8.of_int 2));
    stop_sampling <- (W64.of_int 1);
    if ((filled \ult (W64.of_int 256))) {
      if ((input_offset \ult (W64.of_int ((5 * 168) - 3)))) {
        stop_sampling <- (W64.of_int 0);
      } else {
        
      }
    } else {
      
    }
    while ((stop_sampling <> (W64.of_int 1))) {
      byte0 <- (zeroextu32 randombytes.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      byte1 <- (zeroextu32 randombytes.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      byte2 <- (zeroextu32 randombytes.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      coeff <- byte0;
      byte1 <- (byte1 `<<` (W8.of_int 8));
      coeff <- (coeff `|` byte1);
      byte2 <- (byte2 `<<` (W8.of_int 16));
      coeff <- (coeff `|` byte2);
      coeff <- (coeff `&` (W32.of_int 8388607));
      if ((coeff \ult (W32.of_int 8380417))) {
        polynomial.[(W64.to_uint filled)] <- coeff;
        filled <- (filled + (W64.of_int 1));
      } else {
        
      }
      stop_sampling <- (W64.of_int 0);
      if (((W64.of_int 256) \ule filled)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int ((5 * 168) - 3)) \ule input_offset)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    return (polynomial, filled);
  }
  proc matrix_A__rejection_sample_one_block (polynomial:W32.t Array256.t,
                                             filled:W64.t,
                                             block:W8.t Array168.t) : 
  W32.t Array256.t * W64.t = {
    var block_offset:W64.t;
    var stop_sampling:W8.t;
    var byte0:W32.t;
    var byte1:W32.t;
    var byte2:W32.t;
    var coeff:W32.t;
    block_offset <- (W64.of_int 0);
    stop_sampling <- (W8.of_int 0);
    if (((W64.of_int 256) \ule filled)) {
      stop_sampling <- (W8.of_int 1);
    } else {
      
    }
    while ((stop_sampling <> (W8.of_int 1))) {
      byte0 <- (zeroextu32 block.[(W64.to_uint block_offset)]);
      block_offset <- (block_offset + (W64.of_int 1));
      byte1 <- (zeroextu32 block.[(W64.to_uint block_offset)]);
      block_offset <- (block_offset + (W64.of_int 1));
      byte2 <- (zeroextu32 block.[(W64.to_uint block_offset)]);
      block_offset <- (block_offset + (W64.of_int 1));
      coeff <- byte0;
      byte1 <- (byte1 `<<` (W8.of_int 8));
      coeff <- (coeff `|` byte1);
      byte2 <- (byte2 `<<` (W8.of_int 16));
      coeff <- (coeff `|` byte2);
      coeff <- (coeff `&` (W32.of_int 8388607));
      if ((coeff \ult (W32.of_int 8380417))) {
        polynomial.[(W64.to_uint filled)] <- coeff;
        filled <- (filled + (W64.of_int 1));
      } else {
        
      }
      stop_sampling <- (W8.of_int 0);
      if (((W64.of_int 256) \ule filled)) {
        stop_sampling <- (W8.of_int 1);
      } else {
        if (((W64.of_int 168) \ule block_offset)) {
          stop_sampling <- (W8.of_int 1);
        } else {
          
        }
      }
    }
    return (polynomial, filled);
  }
  proc matrix_A____shake128_squeeze_multiple_blocks_4x (state:W256.t Array25.t,
                                                        b0:W8.t Array848.t,
                                                        b1:W8.t Array848.t,
                                                        b2:W8.t Array848.t,
                                                        b3:W8.t Array848.t) : 
  W256.t Array25.t * W8.t Array848.t * W8.t Array848.t * W8.t Array848.t *
  W8.t Array848.t = {
    var aux:W256.t Array25.t;
    var aux_0:W8.t Array168.t;
    var aux_1:W8.t Array168.t;
    var aux_2:W8.t Array168.t;
    var aux_3:W8.t Array168.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake128_squeezeblock4x (state,
      (Array168.init (fun i_0 => b0.[((i * 168) + i_0)])),
      (Array168.init (fun i_0 => b1.[((i * 168) + i_0)])),
      (Array168.init (fun i_0 => b2.[((i * 168) + i_0)])),
      (Array168.init (fun i_0 => b3.[((i * 168) + i_0)])));
      state <- aux;
      b0 <-
      (Array848.init
      (fun i_0 => (if ((i * 168) <= i_0 < ((i * 168) + 168)) then aux_0.[
                                                                  (i_0 -
                                                                  (i * 168))] else 
                  b0.[i_0]))
      );
      b1 <-
      (Array848.init
      (fun i_0 => (if ((i * 168) <= i_0 < ((i * 168) + 168)) then aux_1.[
                                                                  (i_0 -
                                                                  (i * 168))] else 
                  b1.[i_0]))
      );
      b2 <-
      (Array848.init
      (fun i_0 => (if ((i * 168) <= i_0 < ((i * 168) + 168)) then aux_2.[
                                                                  (i_0 -
                                                                  (i * 168))] else 
                  b2.[i_0]))
      );
      b3 <-
      (Array848.init
      (fun i_0 => (if ((i * 168) <= i_0 < ((i * 168) + 168)) then aux_3.[
                                                                  (i_0 -
                                                                  (i * 168))] else 
                  b3.[i_0]))
      );
      i <- (i + 1);
    }
    return (state, b0, b1, b2, b3);
  }
  proc matrix_A____sample_4_polynomials (rho:W8.t Array32.t,
                                         domain_separators:W16.t Array4.t) : 
  W32.t Array256.t * W32.t Array256.t * W32.t Array256.t * W32.t Array256.t = {
    var aux:W256.t Array25.t;
    var aux_0:W8.t Array168.t;
    var aux_1:W8.t Array168.t;
    var aux_2:W8.t Array168.t;
    var aux_3:W8.t Array168.t;
    var polynomial0:W32.t Array256.t;
    var polynomial1:W32.t Array256.t;
    var polynomial2:W32.t Array256.t;
    var polynomial3:W32.t Array256.t;
    var xof_state:W256.t Array25.t;
    var buf0:W8.t Array848.t;
    var buf1:W8.t Array848.t;
    var buf2:W8.t Array848.t;
    var buf3:W8.t Array848.t;
    var filled:W64.t;
    var filled0:W64.t;
    var filled1:W64.t;
    var filled2:W64.t;
    var filled3:W64.t;
    var stop_sampling:W32.t;
    buf0 <- witness;
    buf1 <- witness;
    buf2 <- witness;
    buf3 <- witness;
    polynomial0 <- witness;
    polynomial1 <- witness;
    polynomial2 <- witness;
    polynomial3 <- witness;
    xof_state <- witness;
    xof_state <@ shake128_absorb_34_4x (xof_state, rho, domain_separators);
    (xof_state, buf0, buf1, buf2, buf3) <@ matrix_A____shake128_squeeze_multiple_blocks_4x (
    xof_state, buf0, buf1, buf2, buf3);
    (polynomial0, filled) <@ matrix_A__rejection_sample_multiple_blocks (
    polynomial0, buf0);
    filled0 <- filled;
    (polynomial1, filled) <@ matrix_A__rejection_sample_multiple_blocks (
    polynomial1, buf1);
    filled1 <- filled;
    (polynomial2, filled) <@ matrix_A__rejection_sample_multiple_blocks (
    polynomial2, buf2);
    filled2 <- filled;
    (polynomial3, filled) <@ matrix_A__rejection_sample_multiple_blocks (
    polynomial3, buf3);
    filled3 <- filled;
    stop_sampling <- (W32.of_int 1);
    if ((filled0 \ult (W64.of_int 256))) {
      stop_sampling <- (W32.of_int 0);
    } else {
      if ((filled1 \ult (W64.of_int 256))) {
        stop_sampling <- (W32.of_int 0);
      } else {
        if ((filled2 \ult (W64.of_int 256))) {
          stop_sampling <- (W32.of_int 0);
        } else {
          if ((filled3 \ult (W64.of_int 256))) {
            stop_sampling <- (W32.of_int 0);
          } else {
            
          }
        }
      }
    }
    while ((stop_sampling <> (W32.of_int 1))) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake128_squeezeblock4x (xof_state,
      (Array168.init (fun i => buf0.[(0 + i)])),
      (Array168.init (fun i => buf1.[(0 + i)])),
      (Array168.init (fun i => buf2.[(0 + i)])),
      (Array168.init (fun i => buf3.[(0 + i)])));
      xof_state <- aux;
      buf0 <-
      (Array848.init
      (fun i => (if (0 <= i < (0 + 168)) then aux_0.[(i - 0)] else buf0.[i]))
      );
      buf1 <-
      (Array848.init
      (fun i => (if (0 <= i < (0 + 168)) then aux_1.[(i - 0)] else buf1.[i]))
      );
      buf2 <-
      (Array848.init
      (fun i => (if (0 <= i < (0 + 168)) then aux_2.[(i - 0)] else buf2.[i]))
      );
      buf3 <-
      (Array848.init
      (fun i => (if (0 <= i < (0 + 168)) then aux_3.[(i - 0)] else buf3.[i]))
      );
      filled <- filled0;
      (polynomial0, filled) <@ matrix_A__rejection_sample_one_block (
      polynomial0, filled, (Array168.init (fun i => buf0.[(0 + i)])));
      filled0 <- filled;
      filled <- filled1;
      (polynomial1, filled) <@ matrix_A__rejection_sample_one_block (
      polynomial1, filled, (Array168.init (fun i => buf1.[(0 + i)])));
      filled1 <- filled;
      filled <- filled2;
      (polynomial2, filled) <@ matrix_A__rejection_sample_one_block (
      polynomial2, filled, (Array168.init (fun i => buf2.[(0 + i)])));
      filled2 <- filled;
      filled <- filled3;
      (polynomial3, filled) <@ matrix_A__rejection_sample_one_block (
      polynomial3, filled, (Array168.init (fun i => buf3.[(0 + i)])));
      filled3 <- filled;
      stop_sampling <- (W32.of_int 1);
      if ((filled0 \ult (W64.of_int 256))) {
        stop_sampling <- (W32.of_int 0);
      } else {
        if ((filled1 \ult (W64.of_int 256))) {
          stop_sampling <- (W32.of_int 0);
        } else {
          if ((filled2 \ult (W64.of_int 256))) {
            stop_sampling <- (W32.of_int 0);
          } else {
            if ((filled3 \ult (W64.of_int 256))) {
              stop_sampling <- (W32.of_int 0);
            } else {
              
            }
          }
        }
      }
    }
    return (polynomial0, polynomial1, polynomial2, polynomial3);
  }
  proc sample____initialize_xof (commitment_hash:W8.t Array48.t) : W256.t Array7.t = {
    var state:W256.t Array7.t;
    state <- witness;
    state <@ shake256_absorb_commitment_hash (commitment_hash);
    return state;
  }
  proc sample____challenge (output_challenge:W32.t Array256.t,
                            seed:W8.t Array48.t) : W32.t Array256.t = {
    var zeros_256:W256.t;
    var state:W256.t Array7.t;
    var xof_block:W8.t Array136.t;
    var signs:W64.t;
    var xof_offset:W64.t;
    var i:W64.t;
    var sample_at:W64.t;
    var coefficient:W32.t;
    var shift:W32.t;
    state <- witness;
    xof_block <- witness;
    zeros_256 <- (set0_256);
    state <@ sample____initialize_xof (seed);
    xof_block <@ shake256_squeeze_block (xof_block, state);
    signs <- (get64_direct (WArray136.init8 (fun i_0 => xof_block.[i_0])) 0);
    xof_offset <- (W64.of_int 8);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int ((256 * 32) %/ 8)))) {
      output_challenge <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct
      (WArray1024.init32 (fun i_0 => output_challenge.[i_0])) (W64.to_uint i)
      zeros_256)));
      i <- (i + (W64.of_int 32));
    }
    i <- (W64.of_int (256 - 49));
    while ((i \ult (W64.of_int 256))) {
      if (((W64.of_int 136) \ule xof_offset)) {
        state <@ shake256_permute (state);
        xof_block <@ shake256_squeeze_block (xof_block, state);
        xof_offset <- (W64.of_int 0);
      } else {
        
      }
      sample_at <- (zeroextu64 xof_block.[(W64.to_uint xof_offset)]);
      xof_offset <- (xof_offset + (W64.of_int 1));
      while ((i \ult sample_at)) {
        if (((W64.of_int 136) \ule xof_offset)) {
          state <@ shake256_permute (state);
          xof_block <@ shake256_squeeze_block (xof_block, state);
          xof_offset <- (W64.of_int 0);
        } else {
          
        }
        sample_at <- (zeroextu64 xof_block.[(W64.to_uint xof_offset)]);
        xof_offset <- (xof_offset + (W64.of_int 1));
      }
      coefficient <- output_challenge.[(W64.to_uint sample_at)];
      output_challenge.[(W64.to_uint i)] <- coefficient;
      shift <- (truncateu32 signs);
      shift <- (shift `&` (W32.of_int 1));
      shift <- (shift `<<` (W8.of_int 1));
      coefficient <- (W32.of_int 1);
      coefficient <- (coefficient - shift);
      output_challenge.[(W64.to_uint sample_at)] <- coefficient;
      signs <- (signs `>>` (W8.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return output_challenge;
  }
  proc __setup_state_to_generate_mask (rho_prime:W8.t Array64.t,
                                       domain_separator:W16.t) : W256.t Array7.t = {
    var state:W256.t Array7.t;
    state <- witness;
    state <@ shake256_absorb_66 (rho_prime, domain_separator);
    return state;
  }
  proc __sample_mask_polynomial_1x (mask:W32.t Array256.t,
                                    rho_prime:W8.t Array64.t,
                                    domain_separator:W16.t) : W32.t Array256.t = {
    var aux:W8.t Array136.t;
    var inc:int;
    var state:W256.t Array7.t;
    var i:int;
    var mask_encoded:W8.t Array680.t;
    mask_encoded <- witness;
    state <- witness;
    state <@ __setup_state_to_generate_mask (rho_prime, domain_separator);
    inc <- (((((20 * 256) %/ 8) + 136) - 1) %/ 136);
    i <- 0;
    while ((i < inc)) {
      aux <@ shake256_squeeze_block ((Array136.init
                                     (fun i_0 => mask_encoded.[((i * 136) +
                                                               i_0)])
                                     ),
      state);
      mask_encoded <-
      (Array680.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  mask_encoded.[i_0]))
      );
      state <@ shake256_permute (state);
      i <- (i + 1);
    }
    mask <@ gamma1____decode_to_polynomial (mask,
    (Array640.init (fun i_0 => mask_encoded.[(0 + i_0)])));
    return mask;
  }
  proc shake256_squeeze_multiple_blocks_4x (state:W256.t Array25.t,
                                            b0:W8.t Array680.t,
                                            b1:W8.t Array680.t,
                                            b2:W8.t Array680.t,
                                            b3:W8.t Array680.t) : W256.t Array25.t *
                                                                  W8.t Array680.t *
                                                                  W8.t Array680.t *
                                                                  W8.t Array680.t *
                                                                  W8.t Array680.t = {
    var aux:W256.t Array25.t;
    var aux_0:W8.t Array136.t;
    var aux_1:W8.t Array136.t;
    var aux_2:W8.t Array136.t;
    var aux_3:W8.t Array136.t;
    var inc:int;
    var i:int;
    inc <- (((((20 * 256) %/ 8) + 136) - 1) %/ 136);
    i <- 0;
    while ((i < inc)) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake256_squeezeblock4x (state,
      (Array136.init (fun i_0 => b0.[((i * 136) + i_0)])),
      (Array136.init (fun i_0 => b1.[((i * 136) + i_0)])),
      (Array136.init (fun i_0 => b2.[((i * 136) + i_0)])),
      (Array136.init (fun i_0 => b3.[((i * 136) + i_0)])));
      state <- aux;
      b0 <-
      (Array680.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux_0.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  b0.[i_0]))
      );
      b1 <-
      (Array680.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux_1.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  b1.[i_0]))
      );
      b2 <-
      (Array680.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux_2.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  b2.[i_0]))
      );
      b3 <-
      (Array680.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux_3.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  b3.[i_0]))
      );
      i <- (i + 1);
    }
    return (state, b0, b1, b2, b3);
  }
  proc __sample_mask_polynomial_4x (rho_prime:W8.t Array64.t,
                                    starting_domain_separator:W16.t) : 
  W32.t Array256.t * W32.t Array256.t * W32.t Array256.t * W32.t Array256.t = {
    var mask0:W32.t Array256.t;
    var mask1:W32.t Array256.t;
    var mask2:W32.t Array256.t;
    var mask3:W32.t Array256.t;
    var xof_state:W256.t Array25.t;
    var mask_encoded0:W8.t Array680.t;
    var mask_encoded1:W8.t Array680.t;
    var mask_encoded2:W8.t Array680.t;
    var mask_encoded3:W8.t Array680.t;
    var  _0:W256.t Array25.t;
     _0 <- witness;
    mask0 <- witness;
    mask1 <- witness;
    mask2 <- witness;
    mask3 <- witness;
    mask_encoded0 <- witness;
    mask_encoded1 <- witness;
    mask_encoded2 <- witness;
    mask_encoded3 <- witness;
    xof_state <- witness;
    xof_state <@ shake256_absorb_66_4x (xof_state, rho_prime,
    starting_domain_separator);
    ( _0, mask_encoded0, mask_encoded1, mask_encoded2, mask_encoded3) <@ 
    shake256_squeeze_multiple_blocks_4x (xof_state, mask_encoded0,
    mask_encoded1, mask_encoded2, mask_encoded3);
    mask0 <@ gamma1____decode_to_polynomial (mask0,
    (Array640.init (fun i => mask_encoded0.[(0 + i)])));
    mask1 <@ gamma1____decode_to_polynomial (mask1,
    (Array640.init (fun i => mask_encoded1.[(0 + i)])));
    mask2 <@ gamma1____decode_to_polynomial (mask2,
    (Array640.init (fun i => mask_encoded2.[(0 + i)])));
    mask3 <@ gamma1____decode_to_polynomial (mask3,
    (Array640.init (fun i => mask_encoded3.[(0 + i)])));
    return (mask0, mask1, mask2, mask3);
  }
  proc polynomial__add (sum_pointer:W32.t Array256.t,
                        lhs_pointer:W32.t Array256.t,
                        rhs_pointer:W32.t Array256.t) : W32.t Array256.t = {
    var lhs:W256.t;
    var rhs:W256.t;
    var sum:W256.t;
    var offset:int;
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      lhs <-
      (get256_direct (WArray1024.init32 (fun i => lhs_pointer.[i])) offset);
      rhs <-
      (get256_direct (WArray1024.init32 (fun i => rhs_pointer.[i])) offset);
      sum <- (VPADD_8u32 lhs rhs);
      sum_pointer <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct
      (WArray1024.init32 (fun i => sum_pointer.[i])) offset sum)));
      offset <- (offset + 32);
    }
    return sum_pointer;
  }
  proc polynomial__subtract (difference_pointer:W32.t Array256.t,
                             lhs_pointer:W32.t Array256.t,
                             rhs_pointer:W32.t Array256.t) : W32.t Array256.t = {
    var lhs:W256.t;
    var rhs:W256.t;
    var difference:W256.t;
    var offset:int;
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      lhs <-
      (get256_direct (WArray1024.init32 (fun i => lhs_pointer.[i])) offset);
      rhs <-
      (get256_direct (WArray1024.init32 (fun i => rhs_pointer.[i])) offset);
      difference <- (VPSUB_8u32 lhs rhs);
      difference_pointer <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct
      (WArray1024.init32 (fun i => difference_pointer.[i])) offset difference
      )));
      offset <- (offset + 32);
    }
    return difference_pointer;
  }
  proc polynomial____pointwise_add_to_total (total:W32.t Array256.t,
                                             polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var lhs:W256.t;
    var rhs:W256.t;
    var sum:W256.t;
    var offset:int;
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      lhs <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset);
      rhs <- (get256_direct (WArray1024.init32 (fun i => total.[i])) offset);
      sum <- (VPADD_8u32 lhs rhs);
      total <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => total.[i]))
      offset sum)));
      offset <- (offset + 32);
    }
    return total;
  }
  proc polynomial____zero (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var zero_u256:W256.t;
    var offset:int;
    zero_u256 <- (set0_256);
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      offset zero_u256)));
      offset <- (offset + 32);
    }
    return polynomial;
  }
  proc polynomial____check_infinity_norm (polynomial:W32.t Array256.t,
                                          threshold:int) : W64.t = {
    var result:W64.t;
    var temp:W64.t;
    var threshold_vector:W256.t;
    var exceeds_any:W256.t;
    var coefficients:W256.t;
    var exceeds:W256.t;
    var msb_mask:W32.t;
    var zf:bool;
    var res8:W8.t;
    var offset:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    temp <- (W64.of_int (threshold - 1));
    threshold_vector <- (zeroextu256 (VMOV_64 temp));
    threshold_vector <- (VPBROADCAST_8u32 (truncateu32 threshold_vector));
    exceeds_any <- (set0_256);
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      coefficients <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset);
      coefficients <- (VPABS_8u32 coefficients);
      exceeds <- (VPCMPGT_8u32 coefficients threshold_vector);
      exceeds_any <- (VPOR_256 exceeds_any exceeds);
      offset <- (offset + 32);
    }
    exceeds_any <- exceeds_any;
    msb_mask <- (MOVEMASK_8u32 exceeds_any);
    ( _0,  _1,  _2,  _3, zf) <- (TEST_32 msb_mask msb_mask);
    res8 <- (SETcc (! zf));
    result <- (zeroextu64 res8);
    return result;
  }
  proc polynomial____shift_coefficients_left (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var coefficients:W256.t;
    var offset:int;
    offset <- 0;
    while ((offset < ((256 * 32) %/ 8))) {
      coefficients <-
      (get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset);
      coefficients <- (VPSLL_8u32 coefficients (W128.of_int 13));
      polynomial <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => polynomial.[i]))
      offset coefficients)));
      offset <- (offset + 32);
    }
    return polynomial;
  }
  proc row_vector__ntt (vector:W32.t Array1280.t) : W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__ntt ((Array256.init
                              (fun i_0 => vector.[((i * 256) + i_0)])));
      vector <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc row_vector____dot_product (output:W32.t Array256.t,
                                  lhs:W32.t Array1280.t,
                                  rhs:W32.t Array1280.t) : W32.t Array256.t = {
    var product:W32.t Array256.t;
    var i:int;
    product <- witness;
    output <@ polynomial____zero (output);
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      (* Erased call to unspill *)
      product <@ polynomial__pointwise_montgomery_multiply_and_reduce (
      product, (Array256.init (fun i_0 => lhs.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => rhs.[((256 * i) + i_0)])));
      (* Erased call to unspill *)
      output <@ polynomial____pointwise_add_to_total (output, product);
      (* Erased call to spill *)
      i <- (i + 1);
    }
    return output;
  }
  proc row_vector____multiply_with_matrix_A (matrix_A:W32.t Array7680.t,
                                             vector:W32.t Array1280.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var out:W32.t Array1536.t;
    var i:int;
    out <- witness;
    i <- 0;
    while ((i < 6)) {
      aux <@ row_vector____dot_product ((Array256.init
                                        (fun i_0 => out.[((256 * i) + i_0)])),
      (Array1280.init (fun i_0 => matrix_A.[(((5 * 256) * i) + i_0)])),
      vector);
      out <-
      (Array1536.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  out.[i_0]))
      );
      i <- (i + 1);
    }
    return out;
  }
  proc row_vector____check_infinity_norm (vector:W32.t Array1280.t,
                                          threshold:int) : W64.t = {
    var result:W64.t;
    var i:int;
    var vector_element:W32.t Array256.t;
    var ret:W64.t;
    vector_element <- witness;
    result <- (W64.of_int 0);
    i <- 0;
    while ((i < 5)) {
      vector_element <-
      (Array256.init (fun i_0 => vector.[((i * 256) + i_0)]));
      ret <@ polynomial____check_infinity_norm (vector_element, threshold);
      result <- (result `|` ret);
      i <- (i + 1);
    }
    return result;
  }
  proc column_vector__reduce32 (vector:W32.t Array1536.t) : W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__reduce32 ((Array256.init
                                   (fun i_0 => vector.[((i * 256) + i_0)])));
      vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector__ntt (vector:W32.t Array1536.t) : W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__ntt ((Array256.init
                              (fun i_0 => vector.[((i * 256) + i_0)])));
      vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector__invert_ntt_montgomery (vector:W32.t Array1536.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__invert_ntt_montgomery ((Array256.init
                                                (fun i_0 => vector.[(
                                                                    (
                                                                    i * 256) +
                                                                    i_0)])
                                                ));
      vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector____power2round (vector:W32.t Array1536.t) : W32.t Array1536.t *
                                                                 W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var aux_0:W32.t Array256.t;
    var t1:W32.t Array1536.t;
    var t0:W32.t Array1536.t;
    var i:int;
    t0 <- witness;
    t1 <- witness;
    i <- 0;
    while ((i < 6)) {
      (aux, aux_0) <@ polynomial____power2round ((Array256.init
                                                 (fun i_0 => t1.[((i * 256) +
                                                                 i_0)])
                                                 ),
      (Array256.init (fun i_0 => t0.[((i * 256) + i_0)])),
      (Array256.init (fun i_0 => vector.[((i * 256) + i_0)])));
      t1 <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  t1.[i_0]))
      );
      t0 <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux_0.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  t0.[i_0]))
      );
      i <- (i + 1);
    }
    return (t1, t0);
  }
  proc column_vector____add (lhs:W32.t Array1536.t, rhs:W32.t Array1536.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var sum:W32.t Array1536.t;
    var i:int;
    sum <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__add ((Array256.init
                              (fun i_0 => sum.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => lhs.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => rhs.[((256 * i) + i_0)])));
      sum <-
      (Array1536.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  sum.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return sum;
  }
  proc column_vector____conditionally_add_modulus (vector:W32.t Array1536.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__conditionally_add_modulus ((Array256.init
                                                    (fun i_0 => vector.[
                                                                ((i * 256) +
                                                                i_0)])
                                                    ));
      vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector____decompose (vector:W32.t Array1536.t) : W32.t Array1536.t *
                                                               W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var aux_0:W32.t Array256.t;
    var low:W32.t Array1536.t;
    var high:W32.t Array1536.t;
    var i:int;
    high <- witness;
    low <- witness;
    i <- 0;
    while ((i < 6)) {
      (aux, aux_0) <@ polynomial__decompose ((Array256.init
                                             (fun i_0 => low.[((i * 256) +
                                                              i_0)])
                                             ),
      (Array256.init (fun i_0 => high.[((i * 256) + i_0)])),
      (Array256.init (fun i_0 => vector.[((i * 256) + i_0)])));
      low <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  low.[i_0]))
      );
      high <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux_0.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  high.[i_0]))
      );
      i <- (i + 1);
    }
    return (low, high);
  }
  proc t0__coefficients_to_bytestream (coefficients:W256.t) : W128.t = {
    var bytestream:W128.t;
    var shifts:W256.t;
    var _bytestream:W256.t;
    var second_4:W256.t;
    shifts <- hALF_OF_BITS_IN_T0_VECTOR;
    coefficients <- (VPSUB_8u32 shifts coefficients);
    shifts <- t0__ENCODING_SHIFTS_TABLE.[0];
    _bytestream <- (VPSLLV_8u32 coefficients shifts);
    _bytestream <- (VPSRL_4u64 _bytestream (W128.of_int 19));
    shifts <- t0__ENCODING_SHIFTS_TABLE.[1];
    _bytestream <- (VPERMD shifts _bytestream);
    shifts <- t0__ENCODING_SHIFTS_TABLE.[2];
    _bytestream <- (VPSLLV_8u32 _bytestream shifts);
    _bytestream <- (VPSRL_4u64 _bytestream (W128.of_int 6));
    second_4 <- (VPSRLDQ_256 _bytestream (W8.of_int 8));
    second_4 <- (VPSLL_4u64 second_4 (W128.of_int 52));
    _bytestream <- (VPADD_4u64 _bytestream second_4);
    shifts <- t0__ENCODING_SHIFTS_TABLE.[3];
    _bytestream <- (VPSRLV_4u64 _bytestream shifts);
    bytestream <- (VEXTRACTI128 _bytestream (W8.of_int 0));
    return bytestream;
  }
  proc t0__encode_polynomial (t0_encoded:W8.t Array416.t, t0:W32.t Array256.t) : 
  W8.t Array416.t = {
    var coefficients:W256.t;
    var bytestream:W128.t;
    var final_encoded_output:W8.t Array16.t;
    var i:int;
    var output_offset:int;
    var input_offset:int;
    final_encoded_output <- witness;
    output_offset <- 0;
    input_offset <- 0;
    while ((input_offset < (((256 * 32) %/ 8) - 32))) {
      coefficients <-
      (get256_direct (WArray1024.init32 (fun i_0 => t0.[i_0])) input_offset);
      bytestream <@ t0__coefficients_to_bytestream (coefficients);
      t0_encoded <-
      (Array416.init
      (WArray416.get8
      (WArray416.set128_direct
      (WArray416.init8 (fun i_0 => t0_encoded.[i_0])) output_offset
      bytestream)));
      output_offset <- (output_offset + 13);
      input_offset <- (input_offset + 32);
    }
    coefficients <-
    (get256_direct (WArray1024.init32 (fun i_0 => t0.[i_0])) input_offset);
    bytestream <@ t0__coefficients_to_bytestream (coefficients);
    final_encoded_output <-
    (Array16.init
    (WArray16.get8
    (WArray16.set128_direct
    (WArray16.init8 (fun i_0 => final_encoded_output.[i_0])) 0 bytestream)));
    i <- 0;
    while ((i < 13)) {
      t0_encoded.[(output_offset + i)] <- final_encoded_output.[i];
      i <- (i + 1);
    }
    return t0_encoded;
  }
  proc t0____encode (encoded:W8.t Array2496.t, t0:W32.t Array1536.t) : 
  W8.t Array2496.t = {
    var aux:W8.t Array416.t;
    var j:int;
    (* Erased call to spill *)
    j <- 0;
    while ((j < 6)) {
      aux <@ t0__encode_polynomial ((Array416.init
                                    (fun i => encoded.[((j *
                                                        ((13 * 256) %/ 8)) +
                                                       i)])
                                    ),
      (Array256.init (fun i => t0.[((256 * j) + i)])));
      encoded <-
      (Array2496.init
      (fun i => (if ((j * ((13 * 256) %/ 8)) <= i < ((j * ((13 * 256) %/ 8)) +
                                                    416)) then aux.[(
                                                                    i -
                                                                    (
                                                                    j *
                                                                    (
                                                                    (13 *
                                                                    256) %/
                                                                    8)))] else 
                encoded.[i]))
      );
      (* Erased call to unspill *)
      j <- (j + 1);
    }
    return encoded;
  }
  proc t0__bytestream_to_coefficients (bytestream:W128.t) : W256.t = {
    var coefficients:W256.t;
    var shifts:W256.t;
    var mask:W256.t;
    coefficients <- (set0_256);
    coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 0));
    coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 1));
    shifts <- t0__DECODING_TABLE.[0];
    coefficients <- (VPSHUFB_256 coefficients shifts);
    shifts <- t0__DECODING_TABLE.[1];
    coefficients <- (VPSRLV_8u32 coefficients shifts);
    mask <- t0__DECODING_TABLE.[2];
    coefficients <- (VPAND_256 coefficients mask);
    shifts <- hALF_OF_BITS_IN_T0_VECTOR;
    coefficients <- (VPSUB_8u32 shifts coefficients);
    return coefficients;
  }
  proc t0____decode_polynomial (t0:W32.t Array256.t,
                                t0_encoded:W8.t Array416.t) : W32.t Array256.t = {
    var bytestream:W128.t;
    var coefficients:W256.t;
    var output_offset:int;
    var input_offset:int;
    output_offset <- 0;
    input_offset <- 0;
    while ((input_offset < (((13 * 256) %/ 8) - 13))) {
      bytestream <-
      (get128_direct (WArray416.init8 (fun i => t0_encoded.[i])) input_offset
      );
      coefficients <@ t0__bytestream_to_coefficients (bytestream);
      t0 <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => t0.[i]))
      output_offset coefficients)));
      output_offset <- (output_offset + 32);
      input_offset <- (input_offset + 13);
    }
    bytestream <-
    (get128_direct (WArray416.init8 (fun i => t0_encoded.[i]))
    (((13 * 256) %/ 8) - 16));
    bytestream <- (VPSRLDQ_128 bytestream (W8.of_int 3));
    coefficients <@ t0__bytestream_to_coefficients (bytestream);
    t0 <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => t0.[i]))
    output_offset coefficients)));
    return t0;
  }
  proc t0__decode (t0:W32.t Array1536.t, encoded:W8.t Array2496.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ t0____decode_polynomial ((Array256.init
                                      (fun i_0 => t0.[((i * 256) + i_0)])),
      (Array416.init (fun i_0 => encoded.[((((13 * 256) %/ 8) * i) + i_0)])));
      t0 <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  t0.[i_0]))
      );
      i <- (i + 1);
    }
    return t0;
  }
  proc t1__coefficients_to_bytestream (coefficients:W256.t) : W128.t = {
    var bytestream:W128.t;
    var shifts:W256.t;
    var _bytestream:W256.t;
    var shifts_128:W128.t;
    shifts <- t1__ENCODING_SHIFTS_TABLE.[0];
    _bytestream <- (VPSLLV_8u32 coefficients shifts);
    _bytestream <- (VPSRL_4u64 _bytestream (W128.of_int 22));
    shifts <- t1__ENCODING_SHIFTS_TABLE.[1];
    _bytestream <- (VPERMD shifts _bytestream);
    shifts <- t1__ENCODING_SHIFTS_TABLE.[2];
    _bytestream <- (VPSLLV_8u32 _bytestream shifts);
    _bytestream <- (VPSRL_4u64 _bytestream (W128.of_int 12));
    _bytestream <- (VPERMQ _bytestream (W8.of_int 8));
    bytestream <- (VEXTRACTI128 _bytestream (W8.of_int 0));
    shifts_128 <- t1__SHUFFLE_TO_GROUP;
    bytestream <- (VPSHUFB_128 bytestream shifts_128);
    return bytestream;
  }
  proc t1__encode_polynomial (t1_encoded:W8.t Array320.t, t1:W32.t Array256.t) : 
  W8.t Array320.t = {
    var coefficients:W256.t;
    var bytestream:W128.t;
    var final_encoded_output:W8.t Array16.t;
    var i:int;
    var output_offset:int;
    var input_offset:int;
    final_encoded_output <- witness;
    output_offset <- 0;
    input_offset <- 0;
    while ((input_offset < (((256 * 32) %/ 8) - 32))) {
      coefficients <-
      (get256_direct (WArray1024.init32 (fun i_0 => t1.[i_0])) input_offset);
      bytestream <@ t1__coefficients_to_bytestream (coefficients);
      t1_encoded <-
      (Array320.init
      (WArray320.get8
      (WArray320.set128_direct
      (WArray320.init8 (fun i_0 => t1_encoded.[i_0])) output_offset
      bytestream)));
      output_offset <- (output_offset + 10);
      input_offset <- (input_offset + 32);
    }
    coefficients <-
    (get256_direct (WArray1024.init32 (fun i_0 => t1.[i_0])) input_offset);
    bytestream <@ t1__coefficients_to_bytestream (coefficients);
    final_encoded_output <-
    (Array16.init
    (WArray16.get8
    (WArray16.set128_direct
    (WArray16.init8 (fun i_0 => final_encoded_output.[i_0])) 0 bytestream)));
    i <- 0;
    while ((i < 10)) {
      t1_encoded.[(output_offset + i)] <- final_encoded_output.[i];
      i <- (i + 1);
    }
    return t1_encoded;
  }
  proc t1____encode (encoded:W8.t Array1920.t, t1:W32.t Array1536.t) : 
  W8.t Array1920.t = {
    var aux:W8.t Array320.t;
    var j:int;
    (* Erased call to spill *)
    j <- 0;
    while ((j < 6)) {
      aux <@ t1__encode_polynomial ((Array320.init
                                    (fun i => encoded.[((j *
                                                        (((23 - 13) * 256) %/
                                                        8)) +
                                                       i)])
                                    ),
      (Array256.init (fun i => t1.[((256 * j) + i)])));
      encoded <-
      (Array1920.init
      (fun i => (if ((j * (((23 - 13) * 256) %/ 8)) <= i < ((j *
                                                            (((23 - 13) *
                                                             256) %/
                                                            8)) +
                                                           320)) then 
                aux.[(i - (j * (((23 - 13) * 256) %/ 8)))] else encoded.[i]))
      );
      (* Erased call to unspill *)
      j <- (j + 1);
    }
    return encoded;
  }
  proc t1__decode_polynomial (t1:W32.t Array256.t, t1_encoded:W8.t Array320.t) : 
  W32.t Array256.t = {
    var coefficients:W256.t;
    var bytestream:W128.t;
    var shifts:W256.t;
    var input_offset:int;
    var output_offset:int;
    coefficients <- (set0_256);
    input_offset <- 0;
    output_offset <- 0;
    while ((output_offset < ((256 - 8) * 4))) {
      bytestream <-
      (get128_direct (WArray320.init8 (fun i => t1_encoded.[i])) input_offset
      );
      input_offset <- (input_offset + 10);
      coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 0));
      coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 1));
      shifts <- t1__DECODING_TABLE.[0];
      coefficients <- (VPSHUFB_256 coefficients shifts);
      shifts <- t1__DECODING_TABLE.[1];
      coefficients <- (VPSRLV_8u32 coefficients shifts);
      coefficients <- (VPAND_256 coefficients t1__mask);
      t1 <-
      (Array256.init
      (WArray1024.get32
      (WArray1024.set256_direct (WArray1024.init32 (fun i => t1.[i]))
      output_offset coefficients)));
      output_offset <- (output_offset + 32);
    }
    bytestream <-
    (get128_direct (WArray320.init8 (fun i => t1_encoded.[i]))
    ((((23 - 13) * 256) %/ 8) - 16));
    bytestream <- (VPSRLDQ_128 bytestream (W8.of_int 6));
    coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 0));
    coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 1));
    shifts <- t1__DECODING_TABLE.[0];
    coefficients <- (VPSHUFB_256 coefficients shifts);
    shifts <- t1__DECODING_TABLE.[1];
    coefficients <- (VPSRLV_8u32 coefficients shifts);
    coefficients <- (VPAND_256 coefficients t1__mask);
    t1 <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => t1.[i]))
    output_offset coefficients)));
    return t1;
  }
  proc signature____encode_hint (signature:W8.t Array3309.t,
                                 hint_0:W32.t Array1536.t) : W8.t Array3309.t = {
    var hint_coefficient:W32.t;
    var condition2:bool;
    var condition1:bool;
    var i:int;
    var hints_written:int;
    var j:int;
    var hint_offset:int;
    i <- 0;
    while ((i < (55 + 6))) {
      signature.[((48 + (5 * ((20 * 256) %/ 8))) + i)] <- (W8.of_int 0);
      i <- (i + 1);
    }
    hints_written <- 0;
    i <- 0;
    condition1 <- (i < 6);
    while (condition1) {
      j <- 0;
      condition2 <- (j < 256);
      while (condition2) {
        hint_offset <- i;
        hint_offset <- (hint_offset `<<` 8);
        hint_offset <- (hint_offset + j);
        hint_coefficient <- hint_0.[hint_offset];
        if ((hint_coefficient <> (W32.of_int 0))) {
          signature.[((48 + (5 * ((20 * 256) %/ 8))) + hints_written)] <-
          (truncateu8 (W64.of_int j));
          hints_written <- (hints_written + 1);
        } else {
          
        }
        j <- (j + 1);
        condition2 <- (j < 256);
      }
      signature.[(((48 + (5 * ((20 * 256) %/ 8))) + 55) + i)] <-
      (truncateu8 (W64.of_int hints_written));
      i <- (i + 1);
      condition1 <- (i < 6);
    }
    return signature;
  }
  proc signature____encode (signature:W8.t Array3309.t,
                            commitment_hash:W8.t Array48.t,
                            signer_response:W32.t Array1280.t,
                            hint_0:W32.t Array1536.t) : W8.t Array3309.t = {
    var aux:W8.t Array3200.t;
    var bytes:W128.t;
    var i:int;
    i <- 0;
    while ((i < 48)) {
      bytes <-
      (get128_direct (WArray48.init8 (fun i_0 => commitment_hash.[i_0])) i);
      signature <-
      (Array3309.init
      (WArray3309.get8
      (WArray3309.set128_direct
      (WArray3309.init8 (fun i_0 => signature.[i_0])) i bytes)));
      i <- (i + 16);
    }
    aux <@ gamma1____encode ((Array3200.init
                             (fun i_0 => signature.[(48 + i_0)])),
    signer_response);
    signature <-
    (Array3309.init
    (fun i_0 => (if (48 <= i_0 < (48 + 3200)) then aux.[(i_0 - 48)] else 
                signature.[i_0]))
    );
    signature <@ signature____encode_hint (signature, hint_0);
    return signature;
  }
  proc signature____decode_hint (hints:W32.t Array1536.t,
                                 hint_encoded:W8.t Array61.t) : W32.t Array1536.t *
                                                                W64.t = {
    var ill_formed_hint:W64.t;
    var hint_at_j:W64.t;
    var hint_at_j_minus_one:W64.t;
    var done2:W8.t;
    var within_bounds:bool;
    var done1:W8.t;
    var hint_0:W64.t;
    var done3:W8.t;
    var previous_true_hints_seen:int;
    var encoded_offset:int;
    var decoded_offset:int;
    var j:int;
    var index:int;
    var current_true_hints_seen:int;
    ill_formed_hint <- (W64.of_int 0);
    previous_true_hints_seen <- 0;
    encoded_offset <- 0;
    within_bounds <- (6 <= encoded_offset);
    done1 <- (SETcc within_bounds);
    done1 <- (done1 `|` (truncateu8 ill_formed_hint));
    while ((done1 = (W8.of_int 0))) {
      decoded_offset <- encoded_offset;
      decoded_offset <- (decoded_offset `<<` 8);
      j <- 0;
      while ((j < 256)) {
        index <- decoded_offset;
        index <- (index + j);
        hints.[index] <- (W32.of_int 0);
        j <- (j + 1);
      }
      current_true_hints_seen <-
      (W64.to_uint (zeroextu64 hint_encoded.[(55 + encoded_offset)]));
      if ((current_true_hints_seen < previous_true_hints_seen)) {
        ill_formed_hint <- (W64.of_int 1);
      } else {
        if ((55 < current_true_hints_seen)) {
          ill_formed_hint <- (W64.of_int 1);
        } else {
          j <- previous_true_hints_seen;
          within_bounds <- (current_true_hints_seen <= j);
          done2 <- (SETcc within_bounds);
          done2 <- (done2 `|` (truncateu8 ill_formed_hint));
          while ((done2 = (W8.of_int 0))) {
            hint_at_j <- (zeroextu64 hint_encoded.[j]);
            if ((previous_true_hints_seen < j)) {
              hint_at_j_minus_one <- (zeroextu64 hint_encoded.[(j - 1)]);
              if ((hint_at_j \ule hint_at_j_minus_one)) {
                ill_formed_hint <- (W64.of_int 1);
              } else {
                
              }
            } else {
              
            }
            if ((ill_formed_hint = (W64.of_int 0))) {
              index <- decoded_offset;
              index <- (index + (W64.to_uint hint_at_j));
              hints.[index] <- (W32.of_int 1);
              j <- (j + 1);
            } else {
              
            }
            within_bounds <- (current_true_hints_seen <= j);
            done2 <- (SETcc within_bounds);
            done2 <- (done2 `|` (truncateu8 ill_formed_hint));
          }
        }
      }
      if ((ill_formed_hint = (W64.of_int 0))) {
        previous_true_hints_seen <- current_true_hints_seen;
        encoded_offset <- (encoded_offset + 1);
      } else {
        
      }
      within_bounds <- (6 <= encoded_offset);
      done1 <- (SETcc within_bounds);
      done1 <- (done1 `|` (truncateu8 ill_formed_hint));
    }
    encoded_offset <- previous_true_hints_seen;
    within_bounds <- (55 <= encoded_offset);
    done3 <- (SETcc within_bounds);
    done3 <- (done3 `|` (truncateu8 ill_formed_hint));
    while ((done3 = (W8.of_int 0))) {
      hint_0 <- (zeroextu64 hint_encoded.[encoded_offset]);
      if ((hint_0 <> (W64.of_int 0))) {
        ill_formed_hint <- (W64.of_int 1);
      } else {
        
      }
      if ((ill_formed_hint = (W64.of_int 0))) {
        encoded_offset <- (encoded_offset + 1);
      } else {
        
      }
      within_bounds <- (55 <= encoded_offset);
      done3 <- (SETcc within_bounds);
      done3 <- (done3 `|` (truncateu8 ill_formed_hint));
    }
    ill_formed_hint <- (- ill_formed_hint);
    return (hints, ill_formed_hint);
  }
  proc signature____decode (signer_response:W32.t Array1280.t,
                            hints:W32.t Array1536.t,
                            signature_encoded:W8.t Array3309.t) : W32.t Array1280.t *
                                                                  W32.t Array1536.t *
                                                                  W64.t = {
    var result:W64.t;
    signer_response <@ gamma1____decode (signer_response,
    (Array3200.init (fun i => signature_encoded.[(48 + i)])));
    (hints, result) <@ signature____decode_hint (hints,
    (Array61.init
    (fun i => signature_encoded.[((48 + (5 * ((20 * 256) %/ 8))) + i)])));
    return (signer_response, hints, result);
  }
  proc s1____encode (encoded:W8.t Array640.t, s1:W32.t Array1280.t) : 
  W8.t Array640.t = {
    var aux:W8.t Array128.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      aux <@ error_polynomial__encode ((Array128.init
                                       (fun i_0 => encoded.[((128 * i) + i_0)])
                                       ),
      (Array256.init (fun i_0 => s1.[((256 * i) + i_0)])));
      encoded <-
      (Array640.init
      (fun i_0 => (if ((128 * i) <= i_0 < ((128 * i) + 128)) then aux.[
                                                                  (i_0 -
                                                                  (128 * i))] else 
                  encoded.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return encoded;
  }
  proc s1____decode (s1:W32.t Array1280.t, encoded:W8.t Array640.t) : 
  W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      aux <@ error_polynomial__decode ((Array256.init
                                       (fun i_0 => s1.[((i * 256) + i_0)])),
      (Array128.init (fun i_0 => encoded.[((128 * i) + i_0)])));
      s1 <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  s1.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return s1;
  }
  proc s2____encode (encoded:W8.t Array768.t, s2:W32.t Array1536.t) : 
  W8.t Array768.t = {
    var aux:W8.t Array128.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ error_polynomial__encode ((Array128.init
                                       (fun i_0 => encoded.[((128 * i) + i_0)])
                                       ),
      (Array256.init (fun i_0 => s2.[((256 * i) + i_0)])));
      encoded <-
      (Array768.init
      (fun i_0 => (if ((128 * i) <= i_0 < ((128 * i) + 128)) then aux.[
                                                                  (i_0 -
                                                                  (128 * i))] else 
                  encoded.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return encoded;
  }
  proc s2____decode (s2:W32.t Array1536.t, encoded:W8.t Array768.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ error_polynomial__decode ((Array256.init
                                       (fun i_0 => s2.[((i * 256) + i_0)])),
      (Array128.init (fun i_0 => encoded.[((128 * i) + i_0)])));
      s2 <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  s2.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return s2;
  }
  proc error_4x____bytestream_to_coefficients (bytestream:W128.t) : W256.t = {
    var coefficients:W256.t;
    var temp:W64.t;
    var mask:W256.t;
    var odd_coefficients:W256.t;
    temp <- (W64.of_int ((1 `<<` 4) - 1));
    mask <- (zeroextu256 (VMOV_64 temp));
    mask <- (VPBROADCAST_32u8 (truncateu8 mask));
    coefficients <- (VPMOVZX_16u8_16u16 bytestream);
    odd_coefficients <- (VPSLL_16u16 coefficients (W128.of_int 4));
    coefficients <- (VPOR_256 coefficients odd_coefficients);
    coefficients <- (VPAND_256 coefficients mask);
    return coefficients;
  }
  proc error_4x____write_out_8_coefficients (error:W32.t Array256.t,
                                             bytes_filled:W64.t,
                                             good_overall:W64.t,
                                             coefficient_block:W128.t) : 
  W32.t Array256.t * W64.t * W64.t = {
    var good:W64.t;
    var shuffle_table_pointer:W8.t Array2048.t;
    var shuffle_table_idx:W64.t;
    var shuffles:W128.t;
    var error_coefficients_128:W128.t;
    var error_coefficients:W256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    shuffle_table_pointer <- witness;
    good <- good_overall;
    good <- (good `&` (W64.of_int 255));
    good_overall <- (good_overall `>>` (W8.of_int 8));
    shuffle_table_pointer <- eRROR_VECTOR_SHUFFLE_TABLE;
    shuffle_table_idx <- good;
    shuffle_table_idx <- (shuffle_table_idx `<<` (W8.of_int 3));
    shuffles <-
    (VMOV_64
    (get64_direct (WArray2048.init8 (fun i => shuffle_table_pointer.[i]))
    (W64.to_uint shuffle_table_idx)));
    error_coefficients_128 <- (VPSHUFB_128 coefficient_block shuffles);
    error_coefficients <-
    (VPMOVSX_8u8_8u32 (truncateu64 error_coefficients_128));
    error <-
    (Array256.init
    (WArray1024.get32
    (WArray1024.set256_direct (WArray1024.init32 (fun i => error.[i]))
    (W64.to_uint bytes_filled) error_coefficients)));
    ( _0,  _1,  _2,  _3,  _4, good) <- (POPCNT_64 good);
    good <- (good `<<` (W8.of_int 2));
    bytes_filled <- (bytes_filled + good);
    return (error, bytes_filled, good_overall);
  }
  proc error_4x__rejection_sample_multiple_blocks (error:W32.t Array256.t,
                                                   randombytes:W8.t Array272.t) : 
  W32.t Array256.t * W64.t = {
    var filled:W64.t;
    var temp:W64.t;
    var eta_0:W256.t;
    var bound:W256.t;
    var bytes_filled:W64.t;
    var xof_offset:W64.t;
    var stop_sampling:W64.t;
    var bytestream:W128.t;
    var coefficients:W256.t;
    var comparisons:W256.t;
    var good_overall:W64.t;
    var coefficient_block:W128.t;
    var coefficient:W32.t;
    var  _0:W64.t;
    temp <- (W64.of_int 4);
    eta_0 <- (zeroextu256 (VMOV_64 temp));
    eta_0 <- (VPBROADCAST_32u8 (truncateu8 eta_0));
    temp <- (W64.of_int 9);
    bound <- (zeroextu256 (VMOV_64 temp));
    bound <- (VPBROADCAST_32u8 (truncateu8 bound));
    bytes_filled <- (W64.of_int 0);
    xof_offset <- (W64.of_int 0);
    stop_sampling <- (W64.of_int 0);
    while ((stop_sampling <> (W64.of_int 1))) {
      bytestream <-
      (get128_direct (WArray272.init8 (fun i => randombytes.[i]))
      (W64.to_uint xof_offset));
      coefficients <@ error_4x____bytestream_to_coefficients (bytestream);
      comparisons <- (VPSUB_32u8 coefficients bound);
      good_overall <- (zeroextu64 (MOVEMASK_32u8 comparisons));
      coefficients <- (VPSUB_32u8 eta_0 coefficients);
      coefficient_block <- (VEXTRACTI128 coefficients (W8.of_int 0));
      good_overall <- good_overall;
      (error, bytes_filled, good_overall) <@ error_4x____write_out_8_coefficients (
      error, bytes_filled, good_overall, coefficient_block);
      xof_offset <- (xof_offset + (W64.of_int 4));
      if ((bytes_filled \ult (W64.of_int (((256 * 32) %/ 8) - 32)))) {
        coefficient_block <- (VPSRLDQ_128 coefficient_block (W8.of_int 8));
        (error, bytes_filled, good_overall) <@ error_4x____write_out_8_coefficients (
        error, bytes_filled, good_overall, coefficient_block);
        xof_offset <- (xof_offset + (W64.of_int 4));
        if ((bytes_filled \ult (W64.of_int (((256 * 32) %/ 8) - 32)))) {
          coefficient_block <- (VEXTRACTI128 coefficients (W8.of_int 1));
          (error, bytes_filled, good_overall) <@ error_4x____write_out_8_coefficients (
          error, bytes_filled, good_overall, coefficient_block);
          xof_offset <- (xof_offset + (W64.of_int 4));
          if ((bytes_filled \ult (W64.of_int (((256 * 32) %/ 8) - 32)))) {
            coefficient_block <-
            (VPSRLDQ_128 coefficient_block (W8.of_int 8));
            (error, bytes_filled,  _0) <@ error_4x____write_out_8_coefficients (
            error, bytes_filled, good_overall, coefficient_block);
            xof_offset <- (xof_offset + (W64.of_int 4));
          } else {
            
          }
        } else {
          
        }
      } else {
        
      }
      if (((W64.of_int (((256 * 32) %/ 8) - 32)) \ule bytes_filled)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int ((2 * 136) - 16)) \ule xof_offset)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    filled <- bytes_filled;
    filled <- (filled `>>` (W8.of_int 2));
    if ((filled \ult (W64.of_int 256))) {
      if ((xof_offset \ult (W64.of_int (2 * 136)))) {
        stop_sampling <- (W64.of_int 0);
      } else {
        
      }
    } else {
      
    }
    while ((stop_sampling <> (W64.of_int 1))) {
      coefficient <- (zeroextu32 randombytes.[(W64.to_uint xof_offset)]);
      coefficient <- (coefficient `&` (W32.of_int 15));
      if ((coefficient \ult (W32.of_int 9))) {
        coefficient <- (coefficient - (W32.of_int 4));
        coefficient <- (- coefficient);
        error.[(W64.to_uint filled)] <- coefficient;
        filled <- (filled + (W64.of_int 1));
      } else {
        
      }
      if ((filled \ult (W64.of_int 256))) {
        coefficient <- (zeroextu32 randombytes.[(W64.to_uint xof_offset)]);
        coefficient <- (coefficient `>>` (W8.of_int 4));
        if ((coefficient \ult (W32.of_int 9))) {
          coefficient <- (coefficient - (W32.of_int 4));
          coefficient <- (- coefficient);
          error.[(W64.to_uint filled)] <- coefficient;
          filled <- (filled + (W64.of_int 1));
        } else {
          
        }
      } else {
        
      }
      xof_offset <- (xof_offset + (W64.of_int 1));
      if (((W64.of_int (2 * 136)) \ule xof_offset)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int 256) \ule filled)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    return (error, filled);
  }
  proc error_4x__rejection_sample_one_block (error:W32.t Array256.t,
                                             filled:W64.t,
                                             randombytes:W8.t Array136.t) : 
  W32.t Array256.t * W64.t = {
    var xof_offset:W64.t;
    var stop_sampling:W64.t;
    var coefficient:W32.t;
    xof_offset <- (W64.of_int 0);
    stop_sampling <- (W64.of_int 0);
    while ((stop_sampling <> (W64.of_int 1))) {
      coefficient <- (zeroextu32 randombytes.[(W64.to_uint xof_offset)]);
      coefficient <- (coefficient `&` (W32.of_int 15));
      if ((coefficient \ult (W32.of_int 9))) {
        coefficient <- (coefficient - (W32.of_int 4));
        coefficient <- (- coefficient);
        error.[(W64.to_uint filled)] <- coefficient;
        filled <- (filled + (W64.of_int 1));
      } else {
        
      }
      if ((filled \ult (W64.of_int 256))) {
        coefficient <- (zeroextu32 randombytes.[(W64.to_uint xof_offset)]);
        coefficient <- (coefficient `>>` (W8.of_int 4));
        if ((coefficient \ult (W32.of_int 9))) {
          coefficient <- (coefficient - (W32.of_int 4));
          coefficient <- (- coefficient);
          error.[(W64.to_uint filled)] <- coefficient;
          filled <- (filled + (W64.of_int 1));
        } else {
          
        }
      } else {
        
      }
      xof_offset <- (xof_offset + (W64.of_int 1));
      if (((W64.of_int 136) \ule xof_offset)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int 256) \ule filled)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    return (error, filled);
  }
  proc error_4x____shake256_squeeze_multiple_blocks_4x (state:W256.t Array25.t,
                                                        b0:W8.t Array272.t,
                                                        b1:W8.t Array272.t,
                                                        b2:W8.t Array272.t,
                                                        b3:W8.t Array272.t) : 
  W256.t Array25.t * W8.t Array272.t * W8.t Array272.t * W8.t Array272.t *
  W8.t Array272.t = {
    var aux:W256.t Array25.t;
    var aux_0:W8.t Array136.t;
    var aux_1:W8.t Array136.t;
    var aux_2:W8.t Array136.t;
    var aux_3:W8.t Array136.t;
    var i:int;
    i <- 0;
    while ((i < 2)) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake256_squeezeblock4x (state,
      (Array136.init (fun i_0 => b0.[((i * 136) + i_0)])),
      (Array136.init (fun i_0 => b1.[((i * 136) + i_0)])),
      (Array136.init (fun i_0 => b2.[((i * 136) + i_0)])),
      (Array136.init (fun i_0 => b3.[((i * 136) + i_0)])));
      state <- aux;
      b0 <-
      (Array272.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux_0.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  b0.[i_0]))
      );
      b1 <-
      (Array272.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux_1.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  b1.[i_0]))
      );
      b2 <-
      (Array272.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux_2.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  b2.[i_0]))
      );
      b3 <-
      (Array272.init
      (fun i_0 => (if ((i * 136) <= i_0 < ((i * 136) + 136)) then aux_3.[
                                                                  (i_0 -
                                                                  (i * 136))] else 
                  b3.[i_0]))
      );
      i <- (i + 1);
    }
    return (state, b0, b1, b2, b3);
  }
  proc error_4x____sample_polynomials (rho_prime:W8.t Array64.t,
                                       starting_domain_separator:W16.t) : 
  W32.t Array256.t * W32.t Array256.t * W32.t Array256.t * W32.t Array256.t = {
    var aux:W256.t Array25.t;
    var aux_0:W8.t Array136.t;
    var aux_1:W8.t Array136.t;
    var aux_2:W8.t Array136.t;
    var aux_3:W8.t Array136.t;
    var polynomial0:W32.t Array256.t;
    var polynomial1:W32.t Array256.t;
    var polynomial2:W32.t Array256.t;
    var polynomial3:W32.t Array256.t;
    var xof_state:W256.t Array25.t;
    var buf0:W8.t Array272.t;
    var buf1:W8.t Array272.t;
    var buf2:W8.t Array272.t;
    var buf3:W8.t Array272.t;
    var filled:W64.t;
    var filled0:W64.t;
    var filled1:W64.t;
    var filled2:W64.t;
    var filled3:W64.t;
    var stop_sampling:W64.t;
    buf0 <- witness;
    buf1 <- witness;
    buf2 <- witness;
    buf3 <- witness;
    polynomial0 <- witness;
    polynomial1 <- witness;
    polynomial2 <- witness;
    polynomial3 <- witness;
    xof_state <- witness;
    xof_state <@ shake256_absorb_66_4x (xof_state, rho_prime,
    starting_domain_separator);
    (xof_state, buf0, buf1, buf2, buf3) <@ error_4x____shake256_squeeze_multiple_blocks_4x (
    xof_state, buf0, buf1, buf2, buf3);
    (polynomial0, filled) <@ error_4x__rejection_sample_multiple_blocks (
    polynomial0, buf0);
    filled0 <- filled;
    (polynomial1, filled) <@ error_4x__rejection_sample_multiple_blocks (
    polynomial1, buf1);
    filled1 <- filled;
    (polynomial2, filled) <@ error_4x__rejection_sample_multiple_blocks (
    polynomial2, buf2);
    filled2 <- filled;
    (polynomial3, filled) <@ error_4x__rejection_sample_multiple_blocks (
    polynomial3, buf3);
    filled3 <- filled;
    stop_sampling <- (W64.of_int 1);
    if ((filled0 \ult (W64.of_int 256))) {
      stop_sampling <- (W64.of_int 0);
    } else {
      if ((filled1 \ult (W64.of_int 256))) {
        stop_sampling <- (W64.of_int 0);
      } else {
        if ((filled2 \ult (W64.of_int 256))) {
          stop_sampling <- (W64.of_int 0);
        } else {
          if ((filled3 \ult (W64.of_int 256))) {
            stop_sampling <- (W64.of_int 0);
          } else {
            
          }
        }
      }
    }
    while ((stop_sampling <> (W64.of_int 1))) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake256_squeezeblock4x (xof_state,
      (Array136.init (fun i => buf0.[(0 + i)])),
      (Array136.init (fun i => buf1.[(0 + i)])),
      (Array136.init (fun i => buf2.[(0 + i)])),
      (Array136.init (fun i => buf3.[(0 + i)])));
      xof_state <- aux;
      buf0 <-
      (Array272.init
      (fun i => (if (0 <= i < (0 + 136)) then aux_0.[(i - 0)] else buf0.[i]))
      );
      buf1 <-
      (Array272.init
      (fun i => (if (0 <= i < (0 + 136)) then aux_1.[(i - 0)] else buf1.[i]))
      );
      buf2 <-
      (Array272.init
      (fun i => (if (0 <= i < (0 + 136)) then aux_2.[(i - 0)] else buf2.[i]))
      );
      buf3 <-
      (Array272.init
      (fun i => (if (0 <= i < (0 + 136)) then aux_3.[(i - 0)] else buf3.[i]))
      );
      if ((filled0 \ult (W64.of_int 256))) {
        filled <- filled0;
        (polynomial0, filled) <@ error_4x__rejection_sample_one_block (
        polynomial0, filled, (Array136.init (fun i => buf0.[(0 + i)])));
        filled0 <- filled;
      } else {
        
      }
      if ((filled1 \ult (W64.of_int 256))) {
        filled <- filled1;
        (polynomial1, filled) <@ error_4x__rejection_sample_one_block (
        polynomial1, filled, (Array136.init (fun i => buf1.[(0 + i)])));
        filled1 <- filled;
      } else {
        
      }
      if ((filled2 \ult (W64.of_int 256))) {
        filled <- filled2;
        (polynomial2, filled) <@ error_4x__rejection_sample_one_block (
        polynomial2, filled, (Array136.init (fun i => buf2.[(0 + i)])));
        filled2 <- filled;
      } else {
        
      }
      if ((filled3 \ult (W64.of_int 256))) {
        filled <- filled3;
        (polynomial3, filled) <@ error_4x__rejection_sample_one_block (
        polynomial3, filled, (Array136.init (fun i => buf3.[(0 + i)])));
        filled3 <- filled;
      } else {
        
      }
      stop_sampling <- (W64.of_int 1);
      if ((filled0 \ult (W64.of_int 256))) {
        stop_sampling <- (W64.of_int 0);
      } else {
        if ((filled1 \ult (W64.of_int 256))) {
          stop_sampling <- (W64.of_int 0);
        } else {
          if ((filled2 \ult (W64.of_int 256))) {
            stop_sampling <- (W64.of_int 0);
          } else {
            if ((filled3 \ult (W64.of_int 256))) {
              stop_sampling <- (W64.of_int 0);
            } else {
              
            }
          }
        }
      }
    }
    return (polynomial0, polynomial1, polynomial2, polynomial3);
  }
  proc sample____error_vectors (rho_prime:W8.t Array64.t) : W32.t Array1280.t *
                                                            W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var aux_0:W32.t Array256.t;
    var aux_1:W32.t Array256.t;
    var aux_2:W32.t Array256.t;
    var s1:W32.t Array1280.t;
    var s2:W32.t Array1536.t;
    var  _0:W32.t Array256.t;
     _0 <- witness;
    s1 <- witness;
    s2 <- witness;
    (aux, aux_0, aux_1, aux_2) <@ error_4x____sample_polynomials (rho_prime,
    (W16.of_int 0));
    s1 <-
    (Array1280.init
    (fun i => (if ((256 * 0) <= i < ((256 * 0) + 256)) then aux.[(i -
                                                                 (256 * 0))] else 
              s1.[i]))
    );
    s1 <-
    (Array1280.init
    (fun i => (if ((256 * 1) <= i < ((256 * 1) + 256)) then aux_0.[(i -
                                                                   (256 * 1))] else 
              s1.[i]))
    );
    s1 <-
    (Array1280.init
    (fun i => (if ((256 * 2) <= i < ((256 * 2) + 256)) then aux_1.[(i -
                                                                   (256 * 2))] else 
              s1.[i]))
    );
    s1 <-
    (Array1280.init
    (fun i => (if ((256 * 3) <= i < ((256 * 3) + 256)) then aux_2.[(i -
                                                                   (256 * 3))] else 
              s1.[i]))
    );
    (aux, aux_0, aux_1, aux_2) <@ error_4x____sample_polynomials (rho_prime,
    (W16.of_int 4));
    s1 <-
    (Array1280.init
    (fun i => (if ((256 * 4) <= i < ((256 * 4) + 256)) then aux.[(i -
                                                                 (256 * 4))] else 
              s1.[i]))
    );
    s2 <-
    (Array1536.init
    (fun i => (if ((256 * 0) <= i < ((256 * 0) + 256)) then aux_0.[(i -
                                                                   (256 * 0))] else 
              s2.[i]))
    );
    s2 <-
    (Array1536.init
    (fun i => (if ((256 * 1) <= i < ((256 * 1) + 256)) then aux_1.[(i -
                                                                   (256 * 1))] else 
              s2.[i]))
    );
    s2 <-
    (Array1536.init
    (fun i => (if ((256 * 2) <= i < ((256 * 2) + 256)) then aux_2.[(i -
                                                                   (256 * 2))] else 
              s2.[i]))
    );
    (aux, aux_0, aux_1, aux_2) <@ error_4x____sample_polynomials (rho_prime,
    (W16.of_int 8));
    s2 <-
    (Array1536.init
    (fun i => (if ((256 * 3) <= i < ((256 * 3) + 256)) then aux.[(i -
                                                                 (256 * 3))] else 
              s2.[i]))
    );
    s2 <-
    (Array1536.init
    (fun i => (if ((256 * 4) <= i < ((256 * 4) + 256)) then aux_0.[(i -
                                                                   (256 * 4))] else 
              s2.[i]))
    );
    s2 <-
    (Array1536.init
    (fun i => (if ((256 * 5) <= i < ((256 * 5) + 256)) then aux_1.[(i -
                                                                   (256 * 5))] else 
              s2.[i]))
    );
     _0 <- aux_2;
    return (s1, s2);
  }
  proc sample____matrix_A (rho:W8.t Array32.t) : W32.t Array7680.t = {
    var aux:W32.t Array256.t;
    var aux_0:W32.t Array256.t;
    var aux_1:W32.t Array256.t;
    var aux_2:W32.t Array256.t;
    var inc:int;
    var matrix_A:W32.t Array7680.t;
    var chunk:int;
    var index:int;
    var lane:int;
    var row:int;
    var column:int;
    var domain_separators:W16.t Array4.t;
    var  _0:W32.t Array256.t;
    var  _1:W32.t Array256.t;
     _0 <- witness;
     _1 <- witness;
    domain_separators <- witness;
    matrix_A <- witness;
    inc <- ((6 * 5) %/ 4);
    chunk <- 0;
    while ((chunk < inc)) {
      index <- (4 * chunk);
      lane <- 0;
      while ((lane < 4)) {
        row <- ((index + lane) %/ 5);
        column <- ((index + lane) %% 5);
        domain_separators.[lane] <-
        (truncateu16 ((W256.of_int (row `<<` 8)) `|` (W256.of_int column)));
        lane <- (lane + 1);
      }
      (aux, aux_0, aux_1, aux_2) <@ matrix_A____sample_4_polynomials (
      rho, domain_separators);
      matrix_A <-
      (Array7680.init
      (fun i => (if (((index + 0) * 256) <= i < (((index + 0) * 256) + 256)) then 
                aux.[(i - ((index + 0) * 256))] else matrix_A.[i]))
      );
      matrix_A <-
      (Array7680.init
      (fun i => (if (((index + 1) * 256) <= i < (((index + 1) * 256) + 256)) then 
                aux_0.[(i - ((index + 1) * 256))] else matrix_A.[i]))
      );
      matrix_A <-
      (Array7680.init
      (fun i => (if (((index + 2) * 256) <= i < (((index + 2) * 256) + 256)) then 
                aux_1.[(i - ((index + 2) * 256))] else matrix_A.[i]))
      );
      matrix_A <-
      (Array7680.init
      (fun i => (if (((index + 3) * 256) <= i < (((index + 3) * 256) + 256)) then 
                aux_2.[(i - ((index + 3) * 256))] else matrix_A.[i]))
      );
      chunk <- (chunk + 1);
    }
    index <- 28;
    lane <- 0;
    while ((lane < 2)) {
      row <- ((index + lane) %/ 5);
      column <- ((index + lane) %% 5);
      domain_separators.[lane] <-
      (truncateu16 ((W256.of_int (row `<<` 8)) `|` (W256.of_int column)));
      lane <- (lane + 1);
    }
    (aux, aux_0, aux_1, aux_2) <@ matrix_A____sample_4_polynomials (rho,
    domain_separators);
    matrix_A <-
    (Array7680.init
    (fun i => (if (((index + 0) * 256) <= i < (((index + 0) * 256) + 256)) then 
              aux.[(i - ((index + 0) * 256))] else matrix_A.[i]))
    );
    matrix_A <-
    (Array7680.init
    (fun i => (if (((index + 1) * 256) <= i < (((index + 1) * 256) + 256)) then 
              aux_0.[(i - ((index + 1) * 256))] else matrix_A.[i]))
    );
     _0 <- aux_1;
     _1 <- aux_2;
    return matrix_A;
  }
  proc __keygen_prf (prf_output:W8.t Array128.t, randomness:W8.t Array32.t) : 
  W8.t Array128.t = {
    var extra:W8.t Array2.t;
    var state:W256.t Array7.t;
    extra <- witness;
    state <- witness;
    extra.[0] <- (W8.of_int 6);
    extra.[1] <- (W8.of_int 5);
    state <@ shake256_absorb_34 (randomness, extra);
    prf_output <@ squeeze_128_bytes (prf_output, state);
    return prf_output;
  }
  proc __compute_t0_t1 (matrix_A:W32.t Array7680.t, s1:W32.t Array1280.t,
                        s2:W32.t Array1536.t) : W32.t Array1536.t *
                                                W32.t Array1536.t = {
    var t1:W32.t Array1536.t;
    var t0:W32.t Array1536.t;
    var t:W32.t Array1536.t;
    t <- witness;
    t0 <- witness;
    t1 <- witness;
    t <@ row_vector____multiply_with_matrix_A (matrix_A, s1);
    t <@ column_vector__reduce32 (t);
    t <@ column_vector__invert_ntt_montgomery (t);
    t <@ column_vector____add (t, s2);
    t <@ column_vector____conditionally_add_modulus (t);
    (t1, t0) <@ column_vector____power2round (t);
    return (t1, t0);
  }
  proc __keygen_internal (verification_key:W8.t Array1952.t,
                          signing_key:W8.t Array4032.t,
                          randomness:W8.t Array32.t) : W8.t Array1952.t *
                                                       W8.t Array4032.t = {
    var aux_1:W8.t Array1920.t;
    var aux_2:W8.t Array2496.t;
    var aux:W8.t Array640.t;
    var aux_0:W8.t Array768.t;
    var prf_output:W8.t Array128.t;
    var seed_for_matrix_A:W8.t Array32.t;
    var matrix_A:W32.t Array7680.t;
    var seed_for_error_vectors:W8.t Array64.t;
    var seed_for_signing:W8.t Array32.t;
    var s1:W32.t Array1280.t;
    var s2:W32.t Array1536.t;
    var copied_32_bytes:W256.t;
    var t1:W32.t Array1536.t;
    var t0:W32.t Array1536.t;
    var verification_key_pointer_copy:W8.t Array1952.t;
    var verification_key_hash:W8.t Array64.t;
    matrix_A <- witness;
    prf_output <- witness;
    s1 <- witness;
    s2 <- witness;
    seed_for_error_vectors <- witness;
    seed_for_matrix_A <- witness;
    seed_for_signing <- witness;
    t0 <- witness;
    t1 <- witness;
    verification_key_hash <- witness;
    verification_key_pointer_copy <- witness;
    (* Erased call to spill *)
    prf_output <@ __keygen_prf (prf_output, randomness);
    seed_for_matrix_A <- (Array32.init (fun i => prf_output.[(0 + i)]));
    matrix_A <@ sample____matrix_A (seed_for_matrix_A);
    seed_for_error_vectors <-
    (Array64.init (fun i => prf_output.[(32 + i)]));
    seed_for_signing <-
    (Array32.init (fun i => prf_output.[((32 + 64) + i)]));
    (s1, s2) <@ sample____error_vectors (seed_for_error_vectors);
    (* Erased call to unspill *)
    copied_32_bytes <-
    (get256_direct (WArray32.init8 (fun i => seed_for_matrix_A.[i])) 0);
    signing_key <-
    (Array4032.init
    (WArray4032.get8
    (WArray4032.set256_direct (WArray4032.init8 (fun i => signing_key.[i])) 0
    copied_32_bytes)));
    verification_key <-
    (Array1952.init
    (WArray1952.get8
    (WArray1952.set256_direct
    (WArray1952.init8 (fun i => verification_key.[i])) 0 copied_32_bytes)));
    copied_32_bytes <-
    (get256_direct (WArray32.init8 (fun i => seed_for_signing.[i])) 0);
    signing_key <-
    (Array4032.init
    (WArray4032.get8
    (WArray4032.set256_direct (WArray4032.init8 (fun i => signing_key.[i]))
    32 copied_32_bytes)));
    aux <@ s1____encode ((Array640.init
                         (fun i => signing_key.[(((32 + 32) + 64) + i)])),
    s1);
    signing_key <-
    (Array4032.init
    (fun i => (if (((32 + 32) + 64) <= i < (((32 + 32) + 64) + 640)) then 
              aux.[(i - ((32 + 32) + 64))] else signing_key.[i]))
    );
    aux_0 <@ s2____encode ((Array768.init
                           (fun i => signing_key.[((((32 + 32) + 64) +
                                                   (5 * 128)) +
                                                  i)])
                           ),
    s2);
    signing_key <-
    (Array4032.init
    (fun i => (if ((((32 + 32) + 64) + (5 * 128)) <= i < ((((32 + 32) + 64) +
                                                          (5 * 128)) +
                                                         768)) then aux_0.[
                                                                    (
                                                                    i -
                                                                    (
                                                                    (
                                                                    (32 + 32) +
                                                                    64) +
                                                                    (5 * 128)))] else 
              signing_key.[i]))
    );
    (* Erased call to spill *)
    s1 <@ row_vector__ntt (s1);
    (t1, t0) <@ __compute_t0_t1 (matrix_A, s1, s2);
    aux_1 <@ t1____encode ((Array1920.init
                           (fun i => verification_key.[(32 + i)])),
    t1);
    verification_key <-
    (Array1952.init
    (fun i => (if (32 <= i < (32 + 1920)) then aux_1.[(i - 32)] else 
              verification_key.[i]))
    );
    verification_key <- verification_key;
    verification_key_pointer_copy <- verification_key;
    (* Erased call to unspill *)
    verification_key_hash <-
    (Array64.init (fun i => signing_key.[(64 + i)]));
    verification_key_hash <@ hash_verification_key (verification_key_hash,
    verification_key_pointer_copy);
    signing_key <-
    (Array4032.init
    (fun i => (if (64 <= i < (64 + 64)) then verification_key_hash.[(i - 64)] else 
              signing_key.[i]))
    );
    aux_2 <@ t0____encode ((Array2496.init
                           (fun i => signing_key.[(((((32 + 32) + 64) +
                                                    (5 * 128)) +
                                                   (6 * 128)) +
                                                  i)])
                           ),
    t0);
    signing_key <-
    (Array4032.init
    (fun i => (if (((((32 + 32) + 64) + (5 * 128)) + (6 * 128)) <= i < 
                  (((((32 + 32) + 64) + (5 * 128)) + (6 * 128)) + 2496)) then 
              aux_2.[(i - ((((32 + 32) + 64) + (5 * 128)) + (6 * 128)))] else 
              signing_key.[i]))
    );
    return (verification_key, signing_key);
  }
  proc sample____mask (rho_prime:W8.t Array64.t, domain_separator:W16.t) : 
  W32.t Array1280.t * W16.t = {
    var aux:W32.t Array256.t;
    var aux_0:W32.t Array256.t;
    var aux_1:W32.t Array256.t;
    var aux_2:W32.t Array256.t;
    var mask:W32.t Array1280.t;
    mask <- witness;
    (aux, aux_0, aux_1, aux_2) <@ __sample_mask_polynomial_4x (rho_prime,
    domain_separator);
    mask <-
    (Array1280.init
    (fun i => (if ((256 * 0) <= i < ((256 * 0) + 256)) then aux.[(i -
                                                                 (256 * 0))] else 
              mask.[i]))
    );
    mask <-
    (Array1280.init
    (fun i => (if ((256 * 1) <= i < ((256 * 1) + 256)) then aux_0.[(i -
                                                                   (256 * 1))] else 
              mask.[i]))
    );
    mask <-
    (Array1280.init
    (fun i => (if ((256 * 2) <= i < ((256 * 2) + 256)) then aux_1.[(i -
                                                                   (256 * 2))] else 
              mask.[i]))
    );
    mask <-
    (Array1280.init
    (fun i => (if ((256 * 3) <= i < ((256 * 3) + 256)) then aux_2.[(i -
                                                                   (256 * 3))] else 
              mask.[i]))
    );
    domain_separator <- (domain_separator + (W16.of_int 4));
    aux <@ __sample_mask_polynomial_1x ((Array256.init
                                        (fun i => mask.[(((256 * 32) %/ 8) +
                                                        i)])
                                        ),
    rho_prime, domain_separator);
    mask <-
    (Array1280.init
    (fun i => (if (((256 * 32) %/ 8) <= i < (((256 * 32) %/ 8) + 256)) then 
              aux.[(i - ((256 * 32) %/ 8))] else mask.[i]))
    );
    domain_separator <- (domain_separator + (W16.of_int 1));
    return (mask, domain_separator);
  }
  proc commitment____encode_polynomial (encoded:W8.t Array128.t,
                                        commitment:W32.t Array256.t) : 
  W8.t Array128.t = {
    var temp:W64.t;
    var shift:W256.t;
    var encoding_shuffles:W256.t;
    var c0:W256.t;
    var c1:W256.t;
    var c2:W256.t;
    var c3:W256.t;
    var c4:W256.t;
    var c5:W256.t;
    var c6:W256.t;
    var c7:W256.t;
    var input_offset:int;
    var output_offset:int;
    temp <- (W64.of_int ((16 `<<` 8) + 1));
    shift <- (zeroextu256 (VMOV_64 temp));
    shift <- (VPBROADCAST_16u16 (truncateu16 shift));
    encoding_shuffles <- commitment__ENCODING_SHUFFLES;
    input_offset <- 0;
    output_offset <- 0;
    while ((output_offset < ((4 * 256) %/ 8))) {
      c0 <-
      (get256_direct (WArray1024.init32 (fun i => commitment.[i]))
      input_offset);
      input_offset <- (input_offset + 32);
      c1 <-
      (get256_direct (WArray1024.init32 (fun i => commitment.[i]))
      input_offset);
      input_offset <- (input_offset + 32);
      c2 <-
      (get256_direct (WArray1024.init32 (fun i => commitment.[i]))
      input_offset);
      input_offset <- (input_offset + 32);
      c3 <-
      (get256_direct (WArray1024.init32 (fun i => commitment.[i]))
      input_offset);
      input_offset <- (input_offset + 32);
      c4 <-
      (get256_direct (WArray1024.init32 (fun i => commitment.[i]))
      input_offset);
      input_offset <- (input_offset + 32);
      c5 <-
      (get256_direct (WArray1024.init32 (fun i => commitment.[i]))
      input_offset);
      input_offset <- (input_offset + 32);
      c6 <-
      (get256_direct (WArray1024.init32 (fun i => commitment.[i]))
      input_offset);
      input_offset <- (input_offset + 32);
      c7 <-
      (get256_direct (WArray1024.init32 (fun i => commitment.[i]))
      input_offset);
      input_offset <- (input_offset + 32);
      c0 <- (VPACKUS_8u32 c0 c1);
      c1 <- (VPACKUS_8u32 c2 c3);
      c2 <- (VPACKUS_8u32 c4 c5);
      c3 <- (VPACKUS_8u32 c6 c7);
      c0 <- (VPACKUS_16u16 c0 c1);
      c1 <- (VPACKUS_16u16 c2 c3);
      c0 <- (VPMADDUBSW_256 c0 shift);
      c1 <- (VPMADDUBSW_256 c1 shift);
      c0 <- (VPACKUS_16u16 c0 c1);
      c0 <- (VPERMQ c0 (W8.of_int 216));
      c0 <- (VPSHUFB_256 c0 encoding_shuffles);
      encoded <-
      (Array128.init
      (WArray128.get8
      (WArray128.set256_direct (WArray128.init8 (fun i => encoded.[i]))
      output_offset c0)));
      output_offset <- (output_offset + 32);
    }
    return encoded;
  }
  proc commitment____encode (commitment:W32.t Array1536.t) : W8.t Array768.t = {
    var aux:W8.t Array128.t;
    var encoded_commitment:W8.t Array768.t;
    var i:int;
    encoded_commitment <- witness;
    i <- 0;
    while ((i < 6)) {
      aux <@ commitment____encode_polynomial ((Array128.init
                                              (fun i_0 => encoded_commitment.[
                                                          ((i *
                                                           ((4 * 256) %/ 8)) +
                                                          i_0)])
                                              ),
      (Array256.init (fun i_0 => commitment.[((i * 256) + i_0)])));
      encoded_commitment <-
      (Array768.init
      (fun i_0 => (if ((i * ((4 * 256) %/ 8)) <= i_0 < ((i *
                                                        ((4 * 256) %/ 8)) +
                                                       128)) then aux.[
                                                                  (i_0 -
                                                                  (i *
                                                                  ((4 * 256) %/
                                                                  8)))] else 
                  encoded_commitment.[i_0]))
      );
      i <- (i + 1);
    }
    return encoded_commitment;
  }
  proc derive_seed_for_mask (k:W8.t Array32.t, randomness:W8.t Array32.t,
                             message_representative:W8.t Array64.t,
                             seed_for_mask:W8.t Array64.t) : W8.t Array64.t = {
    var copied_32_bytes:W256.t;
    var block:W8.t Array128.t;
    var state:W256.t Array7.t;
    block <- witness;
    state <- witness;
    copied_32_bytes <- (get256_direct (WArray32.init8 (fun i => k.[i])) 0);
    block <-
    (Array128.init
    (WArray128.get8
    (WArray128.set256_direct (WArray128.init8 (fun i => block.[i])) 0
    copied_32_bytes)));
    copied_32_bytes <-
    (get256_direct (WArray32.init8 (fun i => randomness.[i])) 0);
    block <-
    (Array128.init
    (WArray128.get8
    (WArray128.set256_direct (WArray128.init8 (fun i => block.[i])) 32
    copied_32_bytes)));
    copied_32_bytes <-
    (get256_direct (WArray64.init8 (fun i => message_representative.[i])) 0);
    block <-
    (Array128.init
    (WArray128.get8
    (WArray128.set256_direct (WArray128.init8 (fun i => block.[i])) 64
    copied_32_bytes)));
    copied_32_bytes <-
    (get256_direct (WArray64.init8 (fun i => message_representative.[i])) 32);
    block <-
    (Array128.init
    (WArray128.get8
    (WArray128.set256_direct (WArray128.init8 (fun i => block.[i])) 96
    copied_32_bytes)));
    state <@ shake256_absorb_128 (block);
    seed_for_mask <@ squeeze_64_bytes (seed_for_mask, state);
    return seed_for_mask;
  }
  proc __compute_signer_response_element (s1_element:W32.t Array256.t,
                                          verifier_challenge:W32.t Array256.t,
                                          mask_element:W32.t Array256.t,
                                          signer_response_element:W32.t Array256.t) : 
  W32.t Array256.t = {
    var cs1:W32.t Array256.t;
    cs1 <- witness;
    cs1 <@ polynomial__pointwise_montgomery_multiply_and_reduce (cs1,
    s1_element, verifier_challenge);
    cs1 <@ polynomial__invert_ntt_montgomery (cs1);
    signer_response_element <@ polynomial__add (signer_response_element, 
    cs1, mask_element);
    signer_response_element <@ polynomial__reduce32 (signer_response_element);
    return signer_response_element;
  }
  proc __compute_z_and_check_norm (s1:W32.t Array1280.t,
                                   verifier_challenge:W32.t Array256.t,
                                   mask:W32.t Array1280.t,
                                   signer_response:W32.t Array1280.t,
                                   infinity_norm_check_result:W64.t) : 
  W32.t Array1280.t * W64.t = {
    var aux:W32.t Array256.t;
    var base:int;
    base <- 0;
    infinity_norm_check_result <- infinity_norm_check_result;
    if ((infinity_norm_check_result <> (W64.of_int 0))) {
      base <- (5 * 256);
    } else {
      
    }
    while ((base < (5 * 256))) {
      aux <@ __compute_signer_response_element ((Array256.init
                                                (fun i => s1.[(base + i)])),
      verifier_challenge, (Array256.init (fun i => mask.[(base + i)])),
      (Array256.init (fun i => signer_response.[(base + i)])));
      signer_response <-
      (Array1280.init
      (fun i => (if (base <= i < (base + 256)) then aux.[(i - base)] else 
                signer_response.[i]))
      );
      infinity_norm_check_result <@ polynomial____check_infinity_norm (
      (Array256.init (fun i => signer_response.[(base + i)])),
      ((1 `<<` 19) - (49 * 4)));
      base <- (base + 256);
      infinity_norm_check_result <- infinity_norm_check_result;
      if ((infinity_norm_check_result <> (W64.of_int 0))) {
        base <- (5 * 256);
      } else {
        
      }
    }
    return (signer_response, infinity_norm_check_result);
  }
  proc __apply_cs2_and_check_norm (w0_minus_cs2:W32.t Array1536.t,
                                   w0:W32.t Array1536.t,
                                   s2:W32.t Array1536.t,
                                   verifier_challenge:W32.t Array256.t,
                                   infinity_norm_check_result:W64.t) : 
  W32.t Array1536.t * W64.t = {
    var aux:W32.t Array256.t;
    var cs2:W32.t Array256.t;
    var base:int;
    cs2 <- witness;
    base <- 0;
    infinity_norm_check_result <- infinity_norm_check_result;
    if ((infinity_norm_check_result <> (W64.of_int 0))) {
      base <- (6 * 256);
    } else {
      
    }
    while ((base < (6 * 256))) {
      cs2 <@ polynomial__pointwise_montgomery_multiply_and_reduce (cs2,
      (Array256.init (fun i => s2.[(base + i)])), verifier_challenge);
      cs2 <@ polynomial__invert_ntt_montgomery (cs2);
      aux <@ polynomial__subtract ((Array256.init
                                   (fun i => w0_minus_cs2.[(base + i)])),
      (Array256.init (fun i => w0.[(base + i)])), cs2);
      w0_minus_cs2 <-
      (Array1536.init
      (fun i => (if (base <= i < (base + 256)) then aux.[(i - base)] else 
                w0_minus_cs2.[i]))
      );
      aux <@ polynomial__reduce32 ((Array256.init
                                   (fun i => w0_minus_cs2.[(base + i)])));
      w0_minus_cs2 <-
      (Array1536.init
      (fun i => (if (base <= i < (base + 256)) then aux.[(i - base)] else 
                w0_minus_cs2.[i]))
      );
      infinity_norm_check_result <@ polynomial____check_infinity_norm (
      (Array256.init (fun i => w0_minus_cs2.[(base + i)])),
      (((8380417 - 1) %/ 32) - (49 * 4)));
      base <- (base + 256);
      infinity_norm_check_result <- infinity_norm_check_result;
      if ((infinity_norm_check_result <> (W64.of_int 0))) {
        base <- (6 * 256);
      } else {
        
      }
    }
    return (w0_minus_cs2, infinity_norm_check_result);
  }
  proc __apply_ct0_and_check_norm (w0_minus_cs2_plus_ct0:W32.t Array1536.t,
                                   w0_minus_cs2:W32.t Array1536.t,
                                   t0:W32.t Array1536.t,
                                   verifier_challenge:W32.t Array256.t,
                                   infinity_norm_check_result:W64.t) : 
  W32.t Array1536.t * W64.t = {
    var aux:W32.t Array256.t;
    var ct0:W32.t Array256.t;
    var base:int;
    ct0 <- witness;
    base <- 0;
    infinity_norm_check_result <- infinity_norm_check_result;
    if ((infinity_norm_check_result <> (W64.of_int 0))) {
      base <- (6 * 256);
    } else {
      
    }
    while ((base < (6 * 256))) {
      ct0 <@ polynomial__pointwise_montgomery_multiply_and_reduce (ct0,
      (Array256.init (fun i => t0.[(base + i)])), verifier_challenge);
      ct0 <@ polynomial__invert_ntt_montgomery (ct0);
      ct0 <@ polynomial__reduce32 (ct0);
      infinity_norm_check_result <@ polynomial____check_infinity_norm (
      ct0, ((8380417 - 1) %/ 32));
      infinity_norm_check_result <- infinity_norm_check_result;
      if ((infinity_norm_check_result = (W64.of_int 0))) {
        aux <@ polynomial__add ((Array256.init
                                (fun i => w0_minus_cs2_plus_ct0.[(base + i)])
                                ),
        (Array256.init (fun i => w0_minus_cs2.[(base + i)])), ct0);
        w0_minus_cs2_plus_ct0 <-
        (Array1536.init
        (fun i => (if (base <= i < (base + 256)) then aux.[(i - base)] else 
                  w0_minus_cs2_plus_ct0.[i]))
        );
      } else {
        
      }
      base <- (base + 256);
      infinity_norm_check_result <- infinity_norm_check_result;
      if ((infinity_norm_check_result <> (W64.of_int 0))) {
        base <- (6 * 256);
      } else {
        
      }
    }
    return (w0_minus_cs2_plus_ct0, infinity_norm_check_result);
  }
  proc __make_hint_vector (w0_minus_cs2_plus_ct0:W32.t Array1536.t,
                           w1:W32.t Array1536.t, hint_0:W32.t Array1536.t,
                           infinity_norm_check_result:W64.t) : W32.t Array1536.t *
                                                               W64.t = {
    var hint_element:W32.t Array256.t;
    var hint_count_exceeded:bool;
    var hint_count_fail:W8.t;
    var hint_count_fail_64:W64.t;
    var total_ones_in_hint:int;
    var base:int;
    var ones_in_hint:int;
    hint_element <- witness;
    total_ones_in_hint <- 0;
    base <- 0;
    infinity_norm_check_result <- infinity_norm_check_result;
    if ((infinity_norm_check_result <> (W64.of_int 0))) {
      base <- (6 * 256);
    } else {
      
    }
    while ((base < (6 * 256))) {
      hint_element <- (Array256.init (fun i => hint_0.[(base + i)]));
      (hint_element, ones_in_hint) <@ polynomial____make_hint (hint_element,
      (Array256.init (fun i => w0_minus_cs2_plus_ct0.[(base + i)])),
      (Array256.init (fun i => w1.[(base + i)])));
      hint_0 <-
      (Array1536.init
      (fun i => (if (base <= i < (base + 256)) then hint_element.[(i - base)] else 
                hint_0.[i]))
      );
      total_ones_in_hint <- (total_ones_in_hint + ones_in_hint);
      base <- (base + 256);
      hint_count_exceeded <- (55 < total_ones_in_hint);
      hint_count_fail <- (SETcc hint_count_exceeded);
      hint_count_fail_64 <- (zeroextu64 hint_count_fail);
      infinity_norm_check_result <-
      (infinity_norm_check_result `|` hint_count_fail_64);
      infinity_norm_check_result <- infinity_norm_check_result;
      if ((infinity_norm_check_result <> (W64.of_int 0))) {
        base <- (6 * 256);
      } else {
        
      }
    }
    return (hint_0, infinity_norm_check_result);
  }
  proc __sign_internal (signature:W8.t Array3309.t,
                        signing_key:W8.t Array4032.t, context_pointer:int,
                        context_size:int, message_pointer:int,
                        message_size:int, randomness:W8.t Array32.t) : 
  W8.t Array3309.t * W64.t = {
    var result:W64.t;
    var seed_for_matrix_A:W8.t Array32.t;
    var matrix_A:W32.t Array7680.t;
    var message_representative:W8.t Array64.t;
    var seed_for_mask:W8.t Array64.t;
    var s1:W32.t Array1280.t;
    var s2:W32.t Array1536.t;
    var t0:W32.t Array1536.t;
    var domain_separator_for_mask:W16.t;
    var exit_rejection_sampling_loop:W64.t;
    var kappa_exceeded:W64.t;
    var last_norm_check_result:W64.t;
    var mask:W32.t Array1280.t;
    var copied_32_bytes:W256.t;
    var mask_as_ntt:W32.t Array1280.t;
    var w:W32.t Array1536.t;
    var w0:W32.t Array1536.t;
    var w1:W32.t Array1536.t;
    var commitment_encoded:W8.t Array768.t;
    var commitment_hash:W8.t Array48.t;
    var verifier_challenge:W32.t Array256.t;
    var infinity_norm_check_result:W64.t;
    var w0_minus_cs2:W32.t Array1536.t;
    var w0_minus_cs2_plus_ct0:W32.t Array1536.t;
    var signer_response:W32.t Array1280.t;
    var hint_0:W32.t Array1536.t;
    var kappa_diff:W32.t;
    var kappa_zf:bool;
    var kappa_bit:W8.t;
    var kappa_bit_64:W64.t;
    var j:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    commitment_encoded <- witness;
    commitment_hash <- witness;
    hint_0 <- witness;
    mask <- witness;
    mask_as_ntt <- witness;
    matrix_A <- witness;
    message_representative <- witness;
    s1 <- witness;
    s2 <- witness;
    seed_for_mask <- witness;
    seed_for_matrix_A <- witness;
    signer_response <- witness;
    t0 <- witness;
    verifier_challenge <- witness;
    w <- witness;
    w0 <- witness;
    w0_minus_cs2 <- witness;
    w0_minus_cs2_plus_ct0 <- witness;
    w1 <- witness;
    (* Erased call to spill *)
    seed_for_matrix_A <- (Array32.init (fun i => signing_key.[(0 + i)]));
    matrix_A <@ sample____matrix_A (seed_for_matrix_A);
    (* Erased call to unspill *)
    message_representative <@ __derive_message_representative ((Array64.init
                                                               (fun i => 
                                                               signing_key.[
                                                               (64 + 
                                                               i)])),
    context_pointer, context_size, message_pointer, message_size);
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    seed_for_mask <@ derive_seed_for_mask ((Array32.init
                                           (fun i => signing_key.[(32 + i)])),
    randomness, message_representative, seed_for_mask);
    (* Erased call to unspill *)
    s1 <@ s1____decode (s1,
    (Array640.init (fun i => signing_key.[(((32 + 32) + 64) + i)])));
    s2 <@ s2____decode (s2,
    (Array768.init
    (fun i => signing_key.[((((32 + 32) + 64) + (5 * 128)) + i)])));
    t0 <@ t0__decode (t0,
    (Array2496.init
    (fun i => signing_key.[(((((32 + 32) + 64) + (5 * 128)) + (6 * 128)) + i)])
    ));
    s1 <@ row_vector__ntt (s1);
    s2 <@ column_vector__ntt (s2);
    t0 <@ column_vector__ntt (t0);
    domain_separator_for_mask <- (W16.of_int 0);
    exit_rejection_sampling_loop <- (W64.of_int 0);
    kappa_exceeded <- (W64.of_int 0);
    last_norm_check_result <- (W64.of_int 1);
    while ((exit_rejection_sampling_loop = (W64.of_int 0))) {
      (mask, domain_separator_for_mask) <@ sample____mask (seed_for_mask,
      domain_separator_for_mask);
      j <- 0;
      while ((j < (5 * ((256 * 32) %/ 8)))) {
        copied_32_bytes <-
        (get256_direct (WArray5120.init32 (fun i => mask.[i])) j);
        mask_as_ntt <-
        (Array1280.init
        (WArray5120.get32
        (WArray5120.set256_direct
        (WArray5120.init32 (fun i => mask_as_ntt.[i])) j copied_32_bytes)));
        j <- (j + 32);
      }
      mask_as_ntt <@ row_vector__ntt (mask_as_ntt);
      w <@ row_vector____multiply_with_matrix_A (matrix_A, mask_as_ntt);
      w <@ column_vector__reduce32 (w);
      w <@ column_vector__invert_ntt_montgomery (w);
      w <@ column_vector____conditionally_add_modulus (w);
      (w0, w1) <@ column_vector____decompose (w);
      commitment_encoded <@ commitment____encode (w1);
      (* Erased call to spill *)
      commitment_hash <@ __derive_commitment_hash (message_representative,
      commitment_encoded);
      verifier_challenge <@ sample____challenge (verifier_challenge,
      commitment_hash);
      (* Erased call to unspill *)
      verifier_challenge <@ polynomial__ntt (verifier_challenge);
      infinity_norm_check_result <- (W64.of_int 0);
      (w0_minus_cs2, infinity_norm_check_result) <@ __apply_cs2_and_check_norm (
      w0_minus_cs2, w0, s2, verifier_challenge, infinity_norm_check_result);
      (w0_minus_cs2_plus_ct0, infinity_norm_check_result) <@ __apply_ct0_and_check_norm (
      w0_minus_cs2_plus_ct0, w0_minus_cs2, t0, verifier_challenge,
      infinity_norm_check_result);
      (signer_response, infinity_norm_check_result) <@ __compute_z_and_check_norm (
      s1, verifier_challenge, mask, signer_response,
      infinity_norm_check_result);
      w0_minus_cs2_plus_ct0 <- w0_minus_cs2_plus_ct0;
      (hint_0, infinity_norm_check_result) <@ __make_hint_vector (w0_minus_cs2_plus_ct0,
      w1, hint_0, infinity_norm_check_result);
      infinity_norm_check_result <- infinity_norm_check_result;
      last_norm_check_result <- infinity_norm_check_result;
      exit_rejection_sampling_loop <- infinity_norm_check_result;
      exit_rejection_sampling_loop <-
      (exit_rejection_sampling_loop `^` (W64.of_int 1));
      kappa_diff <- (zeroextu32 domain_separator_for_mask);
      kappa_diff <- (kappa_diff `^` (W32.of_int (((65535 - 5) %/ 5) * 5)));
      ( _0,  _1,  _2,  _3, kappa_zf) <- (TEST_32 kappa_diff kappa_diff);
      kappa_bit <- (SETcc kappa_zf);
      kappa_bit_64 <- (zeroextu64 kappa_bit);
      kappa_exceeded <- (kappa_exceeded `|` kappa_bit_64);
      exit_rejection_sampling_loop <-
      (exit_rejection_sampling_loop `|` kappa_exceeded);
    }
    (* Erased call to unspill *)
    hint_0 <- hint_0;
    commitment_hash <- commitment_hash;
    signer_response <- signer_response;
    signature <@ signature____encode (signature, commitment_hash,
    signer_response, hint_0);
    result <- last_norm_check_result;
    result <- (result `<<` (W8.of_int 63));
    result <- (result `|>>` (W8.of_int 63));
    return (signature, result);
  }
  proc __compare_commitment_hashes (lhs:W8.t Array48.t, rhs:W8.t Array48.t) : 
  W64.t = {
    var result:W64.t;
    var lhs_bytes:W128.t;
    var rhs_bytes:W128.t;
    var result_vec:W128.t;
    var temp:W128.t;
    var offset:int;
    offset <- 0;
    lhs_bytes <- (get128_direct (WArray48.init8 (fun i => lhs.[i])) offset);
    rhs_bytes <- (get128_direct (WArray48.init8 (fun i => rhs.[i])) offset);
    result_vec <- (VPCMPEQ_16u8 lhs_bytes rhs_bytes);
    offset <- (offset + 16);
    while ((offset < 48)) {
      lhs_bytes <-
      (get128_direct (WArray48.init8 (fun i => lhs.[i])) offset);
      rhs_bytes <-
      (get128_direct (WArray48.init8 (fun i => rhs.[i])) offset);
      temp <- (VPCMPEQ_16u8 lhs_bytes rhs_bytes);
      result_vec <- (VPAND_128 result_vec temp);
      offset <- (offset + 16);
    }
    result <- (zeroextu64 (MOVEMASK_16u8 result_vec));
    result <- result;
    if ((result = (W64.of_int 65535))) {
      result <- (W64.of_int 0);
    } else {
      result <- (W64.of_int (- 1));
    }
    return result;
  }
  proc reconstruct_signer_commitment (t1_encoded:W8.t Array1920.t,
                                      challenge_as_ntt:W32.t Array256.t,
                                      a_times_signer_response:W32.t Array1536.t,
                                      hints:W32.t Array1536.t) : W8.t Array768.t = {
    var commitment_encoded:W8.t Array768.t;
    var i:int;
    var az_element:W32.t Array256.t;
    var t1_element:W32.t Array256.t;
    var c_times_t1:W32.t Array256.t;
    var commitment:W32.t Array1536.t;
    var commitment_element:W32.t Array256.t;
    var hints_element:W32.t Array256.t;
    az_element <- witness;
    c_times_t1 <- witness;
    commitment <- witness;
    commitment_element <- witness;
    commitment_encoded <- witness;
    hints_element <- witness;
    t1_element <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      az_element <-
      (Array256.init (fun i_0 => a_times_signer_response.[((i * 256) + i_0)])
      );
      t1_element <@ t1__decode_polynomial (t1_element,
      (Array320.init
      (fun i_0 => t1_encoded.[(((((23 - 13) * 256) %/ 8) * i) + i_0)])));
      t1_element <@ polynomial____shift_coefficients_left (t1_element);
      t1_element <@ polynomial__ntt (t1_element);
      (* Erased call to unspill *)
      c_times_t1 <@ polynomial__pointwise_montgomery_multiply_and_reduce (
      c_times_t1, challenge_as_ntt, t1_element);
      commitment_element <-
      (Array256.init (fun i_0 => commitment.[((i * 256) + i_0)]));
      commitment_element <@ polynomial__subtract (commitment_element,
      az_element, c_times_t1);
      commitment_element <@ polynomial__reduce32 (commitment_element);
      commitment_element <@ polynomial__invert_ntt_montgomery (commitment_element);
      commitment_element <@ polynomial__conditionally_add_modulus (commitment_element);
      hints_element <-
      (Array256.init (fun i_0 => hints.[((i * 256) + i_0)]));
      commitment_element <@ polynomial__use_hints (commitment_element,
      hints_element);
      commitment <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then commitment_element.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  commitment.[i_0]))
      );
      i <- (i + 1);
    }
    commitment_encoded <@ commitment____encode (commitment);
    return commitment_encoded;
  }
  proc __verify_internal (verification_key:W8.t Array1952.t,
                          context_pointer:int, context_size:int,
                          message_pointer:int, message_size:int,
                          signature_encoded:W8.t Array3309.t) : W64.t = {
    var result:W64.t;
    var signer_response:W32.t Array1280.t;
    var hints:W32.t Array1536.t;
    var result1:W64.t;
    var result2:W64.t;
    var matrix_A:W32.t Array7680.t;
    var a_times_signer_response:W32.t Array1536.t;
    var challenge:W32.t Array256.t;
    var reconstructed_signer_commitment:W8.t Array768.t;
    var verification_key_hash:W8.t Array64.t;
    var message_representative:W8.t Array64.t;
    var expected_commitment_hash:W8.t Array48.t;
    a_times_signer_response <- witness;
    challenge <- witness;
    expected_commitment_hash <- witness;
    hints <- witness;
    matrix_A <- witness;
    message_representative <- witness;
    reconstructed_signer_commitment <- witness;
    signer_response <- witness;
    verification_key_hash <- witness;
    (* Erased call to spill *)
    (signer_response, hints, result1) <@ signature____decode (signer_response,
    hints, signature_encoded);
    result2 <@ row_vector____check_infinity_norm (signer_response,
    ((1 `<<` 19) - (49 * 4)));
    result <- (result1 `|` result2);
    if ((result = (W64.of_int 0))) {
      (* Erased call to spill *)
      matrix_A <@ sample____matrix_A ((Array32.init
                                      (fun i => verification_key.[(0 + i)])));
      signer_response <@ row_vector__ntt (signer_response);
      a_times_signer_response <@ row_vector____multiply_with_matrix_A (
      matrix_A, signer_response);
      (* Erased call to unspill *)
      challenge <@ sample____challenge (challenge,
      (Array48.init (fun i => signature_encoded.[(0 + i)])));
      challenge <@ polynomial__ntt (challenge);
      (* Erased call to unspill *)
      reconstructed_signer_commitment <@ reconstruct_signer_commitment (
      (Array1920.init (fun i => verification_key.[(32 + i)])), challenge,
      a_times_signer_response, hints);
      (* Erased call to unspill *)
      verification_key_hash <@ hash_verification_key (verification_key_hash,
      verification_key);
      (* Erased call to unspill *)
      message_representative <@ __derive_message_representative (verification_key_hash,
      context_pointer, context_size, message_pointer, message_size);
      expected_commitment_hash <@ __derive_commitment_hash (message_representative,
      reconstructed_signer_commitment);
      (* Erased call to unspill *)
      result <@ __compare_commitment_hashes (expected_commitment_hash,
      (Array48.init (fun i => signature_encoded.[(0 + i)])));
    } else {
      
    }
    return result;
  }
  proc ml_dsa_65_keygen (verification_key:W8.t Array1952.t,
                         signing_key:W8.t Array4032.t,
                         randomness:W8.t Array32.t) : W8.t Array1952.t *
                                                      W8.t Array4032.t = {
    
    (* Erased call to spill *)
    (verification_key, signing_key) <@ __keygen_internal (verification_key,
    signing_key, randomness);
    return (verification_key, signing_key);
  }
  proc ml_dsa_65_sign (signature:W8.t Array3309.t,
                       signing_key:W8.t Array4032.t, context:W64.t Array2.t,
                       message_pointer:int, message_size:int,
                       randomness:W8.t Array32.t) : W8.t Array3309.t * W64.t = {
    var result:W64.t;
    var context_pointer:int;
    var context_size:int;
    context_pointer <- (W64.to_uint context.[0]);
    context_size <- (W64.to_uint context.[1]);
    if ((context_size <= 255)) {
      (signature, result) <@ __sign_internal (signature, signing_key,
      context_pointer, context_size, message_pointer, message_size,
      randomness);
    } else {
      result <- (W64.of_int (- 1));
    }
    return (signature, result);
  }
  proc ml_dsa_65_verify (verification_key:W8.t Array1952.t,
                         context:W64.t Array2.t, message_pointer:int,
                         message_size:int, signature:W8.t Array3309.t) : 
  W64.t = {
    var verification_result:W64.t;
    var context_pointer:int;
    var context_size:int;
    context_pointer <- (W64.to_uint context.[0]);
    context_size <- (W64.to_uint context.[1]);
    if ((context_size <= 255)) {
      verification_result <@ __verify_internal (verification_key,
      context_pointer, context_size, message_pointer, message_size,
      signature);
    } else {
      verification_result <- (W64.of_int (- 1));
    }
    return verification_result;
  }
}.
