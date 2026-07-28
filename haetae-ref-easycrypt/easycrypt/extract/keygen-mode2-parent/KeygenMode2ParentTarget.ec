require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array5 Array24 Array25 Array32 Array128 Array256 Array512 Array1024 Array2048
Array2080 Array2752 Array8192 WArray192 WArray512 WArray1024 WArray2048
BArray20 BArray32 BArray40 BArray128 BArray192 BArray200 BArray512 BArray1024
BArray2048 BArray2080 BArray2752 BArray8192 BArray32768 SBArray128_32
SBArray8192_1024.

abbrev jfft_brv8 =
(BArray512.of_list16
[(W16.of_int 0); (W16.of_int 128); (W16.of_int 64); (W16.of_int 192);
(W16.of_int 32); (W16.of_int 160); (W16.of_int 96); (W16.of_int 224);
(W16.of_int 16); (W16.of_int 144); (W16.of_int 80); (W16.of_int 208);
(W16.of_int 48); (W16.of_int 176); (W16.of_int 112); (W16.of_int 240);
(W16.of_int 8); (W16.of_int 136); (W16.of_int 72); (W16.of_int 200);
(W16.of_int 40); (W16.of_int 168); (W16.of_int 104); (W16.of_int 232);
(W16.of_int 24); (W16.of_int 152); (W16.of_int 88); (W16.of_int 216);
(W16.of_int 56); (W16.of_int 184); (W16.of_int 120); (W16.of_int 248);
(W16.of_int 4); (W16.of_int 132); (W16.of_int 68); (W16.of_int 196);
(W16.of_int 36); (W16.of_int 164); (W16.of_int 100); (W16.of_int 228);
(W16.of_int 20); (W16.of_int 148); (W16.of_int 84); (W16.of_int 212);
(W16.of_int 52); (W16.of_int 180); (W16.of_int 116); (W16.of_int 244);
(W16.of_int 12); (W16.of_int 140); (W16.of_int 76); (W16.of_int 204);
(W16.of_int 44); (W16.of_int 172); (W16.of_int 108); (W16.of_int 236);
(W16.of_int 28); (W16.of_int 156); (W16.of_int 92); (W16.of_int 220);
(W16.of_int 60); (W16.of_int 188); (W16.of_int 124); (W16.of_int 252);
(W16.of_int 2); (W16.of_int 130); (W16.of_int 66); (W16.of_int 194);
(W16.of_int 34); (W16.of_int 162); (W16.of_int 98); (W16.of_int 226);
(W16.of_int 18); (W16.of_int 146); (W16.of_int 82); (W16.of_int 210);
(W16.of_int 50); (W16.of_int 178); (W16.of_int 114); (W16.of_int 242);
(W16.of_int 10); (W16.of_int 138); (W16.of_int 74); (W16.of_int 202);
(W16.of_int 42); (W16.of_int 170); (W16.of_int 106); (W16.of_int 234);
(W16.of_int 26); (W16.of_int 154); (W16.of_int 90); (W16.of_int 218);
(W16.of_int 58); (W16.of_int 186); (W16.of_int 122); (W16.of_int 250);
(W16.of_int 6); (W16.of_int 134); (W16.of_int 70); (W16.of_int 198);
(W16.of_int 38); (W16.of_int 166); (W16.of_int 102); (W16.of_int 230);
(W16.of_int 22); (W16.of_int 150); (W16.of_int 86); (W16.of_int 214);
(W16.of_int 54); (W16.of_int 182); (W16.of_int 118); (W16.of_int 246);
(W16.of_int 14); (W16.of_int 142); (W16.of_int 78); (W16.of_int 206);
(W16.of_int 46); (W16.of_int 174); (W16.of_int 110); (W16.of_int 238);
(W16.of_int 30); (W16.of_int 158); (W16.of_int 94); (W16.of_int 222);
(W16.of_int 62); (W16.of_int 190); (W16.of_int 126); (W16.of_int 254);
(W16.of_int 1); (W16.of_int 129); (W16.of_int 65); (W16.of_int 193);
(W16.of_int 33); (W16.of_int 161); (W16.of_int 97); (W16.of_int 225);
(W16.of_int 17); (W16.of_int 145); (W16.of_int 81); (W16.of_int 209);
(W16.of_int 49); (W16.of_int 177); (W16.of_int 113); (W16.of_int 241);
(W16.of_int 9); (W16.of_int 137); (W16.of_int 73); (W16.of_int 201);
(W16.of_int 41); (W16.of_int 169); (W16.of_int 105); (W16.of_int 233);
(W16.of_int 25); (W16.of_int 153); (W16.of_int 89); (W16.of_int 217);
(W16.of_int 57); (W16.of_int 185); (W16.of_int 121); (W16.of_int 249);
(W16.of_int 5); (W16.of_int 133); (W16.of_int 69); (W16.of_int 197);
(W16.of_int 37); (W16.of_int 165); (W16.of_int 101); (W16.of_int 229);
(W16.of_int 21); (W16.of_int 149); (W16.of_int 85); (W16.of_int 213);
(W16.of_int 53); (W16.of_int 181); (W16.of_int 117); (W16.of_int 245);
(W16.of_int 13); (W16.of_int 141); (W16.of_int 77); (W16.of_int 205);
(W16.of_int 45); (W16.of_int 173); (W16.of_int 109); (W16.of_int 237);
(W16.of_int 29); (W16.of_int 157); (W16.of_int 93); (W16.of_int 221);
(W16.of_int 61); (W16.of_int 189); (W16.of_int 125); (W16.of_int 253);
(W16.of_int 3); (W16.of_int 131); (W16.of_int 67); (W16.of_int 195);
(W16.of_int 35); (W16.of_int 163); (W16.of_int 99); (W16.of_int 227);
(W16.of_int 19); (W16.of_int 147); (W16.of_int 83); (W16.of_int 211);
(W16.of_int 51); (W16.of_int 179); (W16.of_int 115); (W16.of_int 243);
(W16.of_int 11); (W16.of_int 139); (W16.of_int 75); (W16.of_int 203);
(W16.of_int 43); (W16.of_int 171); (W16.of_int 107); (W16.of_int 235);
(W16.of_int 27); (W16.of_int 155); (W16.of_int 91); (W16.of_int 219);
(W16.of_int 59); (W16.of_int 187); (W16.of_int 123); (W16.of_int 251);
(W16.of_int 7); (W16.of_int 135); (W16.of_int 71); (W16.of_int 199);
(W16.of_int 39); (W16.of_int 167); (W16.of_int 103); (W16.of_int 231);
(W16.of_int 23); (W16.of_int 151); (W16.of_int 87); (W16.of_int 215);
(W16.of_int 55); (W16.of_int 183); (W16.of_int 119); (W16.of_int 247);
(W16.of_int 15); (W16.of_int 143); (W16.of_int 79); (W16.of_int 207);
(W16.of_int 47); (W16.of_int 175); (W16.of_int 111); (W16.of_int 239);
(W16.of_int 31); (W16.of_int 159); (W16.of_int 95); (W16.of_int 223);
(W16.of_int 63); (W16.of_int 191); (W16.of_int 127); (W16.of_int 255)]).

abbrev jfft_roots =
(BArray2048.of_list32
[(W32.of_int 65536); (W32.of_int 0); (W32.of_int 65531); (W32.of_int (-804));
(W32.of_int 65516); (W32.of_int (-1608)); (W32.of_int 65492);
(W32.of_int (-2412)); (W32.of_int 65457); (W32.of_int (-3216));
(W32.of_int 65413); (W32.of_int (-4019)); (W32.of_int 65358);
(W32.of_int (-4821)); (W32.of_int 65294); (W32.of_int (-5623));
(W32.of_int 65220); (W32.of_int (-6424)); (W32.of_int 65137);
(W32.of_int (-7224)); (W32.of_int 65043); (W32.of_int (-8022));
(W32.of_int 64940); (W32.of_int (-8820)); (W32.of_int 64827);
(W32.of_int (-9616)); (W32.of_int 64704); (W32.of_int (-10411));
(W32.of_int 64571); (W32.of_int (-11204)); (W32.of_int 64429);
(W32.of_int (-11996)); (W32.of_int 64277); (W32.of_int (-12785));
(W32.of_int 64115); (W32.of_int (-13573)); (W32.of_int 63944);
(W32.of_int (-14359)); (W32.of_int 63763); (W32.of_int (-15143));
(W32.of_int 63572); (W32.of_int (-15924)); (W32.of_int 63372);
(W32.of_int (-16703)); (W32.of_int 63162); (W32.of_int (-17479));
(W32.of_int 62943); (W32.of_int (-18253)); (W32.of_int 62714);
(W32.of_int (-19024)); (W32.of_int 62476); (W32.of_int (-19792));
(W32.of_int 62228); (W32.of_int (-20557)); (W32.of_int 61971);
(W32.of_int (-21320)); (W32.of_int 61705); (W32.of_int (-22078));
(W32.of_int 61429); (W32.of_int (-22834)); (W32.of_int 61145);
(W32.of_int (-23586)); (W32.of_int 60851); (W32.of_int (-24335));
(W32.of_int 60547); (W32.of_int (-25080)); (W32.of_int 60235);
(W32.of_int (-25821)); (W32.of_int 59914); (W32.of_int (-26558));
(W32.of_int 59583); (W32.of_int (-27291)); (W32.of_int 59244);
(W32.of_int (-28020)); (W32.of_int 58896); (W32.of_int (-28745));
(W32.of_int 58538); (W32.of_int (-29466)); (W32.of_int 58172);
(W32.of_int (-30182)); (W32.of_int 57798); (W32.of_int (-30893));
(W32.of_int 57414); (W32.of_int (-31600)); (W32.of_int 57022);
(W32.of_int (-32303)); (W32.of_int 56621); (W32.of_int (-33000));
(W32.of_int 56212); (W32.of_int (-33692)); (W32.of_int 55794);
(W32.of_int (-34380)); (W32.of_int 55368); (W32.of_int (-35062));
(W32.of_int 54934); (W32.of_int (-35738)); (W32.of_int 54491);
(W32.of_int (-36410)); (W32.of_int 54040); (W32.of_int (-37076));
(W32.of_int 53581); (W32.of_int (-37736)); (W32.of_int 53114);
(W32.of_int (-38391)); (W32.of_int 52639); (W32.of_int (-39040));
(W32.of_int 52156); (W32.of_int (-39683)); (W32.of_int 51665);
(W32.of_int (-40320)); (W32.of_int 51166); (W32.of_int (-40951));
(W32.of_int 50660); (W32.of_int (-41576)); (W32.of_int 50146);
(W32.of_int (-42194)); (W32.of_int 49624); (W32.of_int (-42806));
(W32.of_int 49095); (W32.of_int (-43412)); (W32.of_int 48559);
(W32.of_int (-44011)); (W32.of_int 48015); (W32.of_int (-44604));
(W32.of_int 47464); (W32.of_int (-45190)); (W32.of_int 46906);
(W32.of_int (-45769)); (W32.of_int 46341); (W32.of_int (-46341));
(W32.of_int 45769); (W32.of_int (-46906)); (W32.of_int 45190);
(W32.of_int (-47464)); (W32.of_int 44604); (W32.of_int (-48015));
(W32.of_int 44011); (W32.of_int (-48559)); (W32.of_int 43412);
(W32.of_int (-49095)); (W32.of_int 42806); (W32.of_int (-49624));
(W32.of_int 42194); (W32.of_int (-50146)); (W32.of_int 41576);
(W32.of_int (-50660)); (W32.of_int 40951); (W32.of_int (-51166));
(W32.of_int 40320); (W32.of_int (-51665)); (W32.of_int 39683);
(W32.of_int (-52156)); (W32.of_int 39040); (W32.of_int (-52639));
(W32.of_int 38391); (W32.of_int (-53114)); (W32.of_int 37736);
(W32.of_int (-53581)); (W32.of_int 37076); (W32.of_int (-54040));
(W32.of_int 36410); (W32.of_int (-54491)); (W32.of_int 35738);
(W32.of_int (-54934)); (W32.of_int 35062); (W32.of_int (-55368));
(W32.of_int 34380); (W32.of_int (-55794)); (W32.of_int 33692);
(W32.of_int (-56212)); (W32.of_int 33000); (W32.of_int (-56621));
(W32.of_int 32303); (W32.of_int (-57022)); (W32.of_int 31600);
(W32.of_int (-57414)); (W32.of_int 30893); (W32.of_int (-57798));
(W32.of_int 30182); (W32.of_int (-58172)); (W32.of_int 29466);
(W32.of_int (-58538)); (W32.of_int 28745); (W32.of_int (-58896));
(W32.of_int 28020); (W32.of_int (-59244)); (W32.of_int 27291);
(W32.of_int (-59583)); (W32.of_int 26558); (W32.of_int (-59914));
(W32.of_int 25821); (W32.of_int (-60235)); (W32.of_int 25080);
(W32.of_int (-60547)); (W32.of_int 24335); (W32.of_int (-60851));
(W32.of_int 23586); (W32.of_int (-61145)); (W32.of_int 22834);
(W32.of_int (-61429)); (W32.of_int 22078); (W32.of_int (-61705));
(W32.of_int 21320); (W32.of_int (-61971)); (W32.of_int 20557);
(W32.of_int (-62228)); (W32.of_int 19792); (W32.of_int (-62476));
(W32.of_int 19024); (W32.of_int (-62714)); (W32.of_int 18253);
(W32.of_int (-62943)); (W32.of_int 17479); (W32.of_int (-63162));
(W32.of_int 16703); (W32.of_int (-63372)); (W32.of_int 15924);
(W32.of_int (-63572)); (W32.of_int 15143); (W32.of_int (-63763));
(W32.of_int 14359); (W32.of_int (-63944)); (W32.of_int 13573);
(W32.of_int (-64115)); (W32.of_int 12785); (W32.of_int (-64277));
(W32.of_int 11996); (W32.of_int (-64429)); (W32.of_int 11204);
(W32.of_int (-64571)); (W32.of_int 10411); (W32.of_int (-64704));
(W32.of_int 9616); (W32.of_int (-64827)); (W32.of_int 8820);
(W32.of_int (-64940)); (W32.of_int 8022); (W32.of_int (-65043));
(W32.of_int 7224); (W32.of_int (-65137)); (W32.of_int 6424);
(W32.of_int (-65220)); (W32.of_int 5623); (W32.of_int (-65294));
(W32.of_int 4821); (W32.of_int (-65358)); (W32.of_int 4019);
(W32.of_int (-65413)); (W32.of_int 3216); (W32.of_int (-65457));
(W32.of_int 2412); (W32.of_int (-65492)); (W32.of_int 1608);
(W32.of_int (-65516)); (W32.of_int 804); (W32.of_int (-65531));
(W32.of_int 0); (W32.of_int (-65536)); (W32.of_int (-804));
(W32.of_int (-65531)); (W32.of_int (-1608)); (W32.of_int (-65516));
(W32.of_int (-2412)); (W32.of_int (-65492)); (W32.of_int (-3216));
(W32.of_int (-65457)); (W32.of_int (-4019)); (W32.of_int (-65413));
(W32.of_int (-4821)); (W32.of_int (-65358)); (W32.of_int (-5623));
(W32.of_int (-65294)); (W32.of_int (-6424)); (W32.of_int (-65220));
(W32.of_int (-7224)); (W32.of_int (-65137)); (W32.of_int (-8022));
(W32.of_int (-65043)); (W32.of_int (-8820)); (W32.of_int (-64940));
(W32.of_int (-9616)); (W32.of_int (-64827)); (W32.of_int (-10411));
(W32.of_int (-64704)); (W32.of_int (-11204)); (W32.of_int (-64571));
(W32.of_int (-11996)); (W32.of_int (-64429)); (W32.of_int (-12785));
(W32.of_int (-64277)); (W32.of_int (-13573)); (W32.of_int (-64115));
(W32.of_int (-14359)); (W32.of_int (-63944)); (W32.of_int (-15143));
(W32.of_int (-63763)); (W32.of_int (-15924)); (W32.of_int (-63572));
(W32.of_int (-16703)); (W32.of_int (-63372)); (W32.of_int (-17479));
(W32.of_int (-63162)); (W32.of_int (-18253)); (W32.of_int (-62943));
(W32.of_int (-19024)); (W32.of_int (-62714)); (W32.of_int (-19792));
(W32.of_int (-62476)); (W32.of_int (-20557)); (W32.of_int (-62228));
(W32.of_int (-21320)); (W32.of_int (-61971)); (W32.of_int (-22078));
(W32.of_int (-61705)); (W32.of_int (-22834)); (W32.of_int (-61429));
(W32.of_int (-23586)); (W32.of_int (-61145)); (W32.of_int (-24335));
(W32.of_int (-60851)); (W32.of_int (-25080)); (W32.of_int (-60547));
(W32.of_int (-25821)); (W32.of_int (-60235)); (W32.of_int (-26558));
(W32.of_int (-59914)); (W32.of_int (-27291)); (W32.of_int (-59583));
(W32.of_int (-28020)); (W32.of_int (-59244)); (W32.of_int (-28745));
(W32.of_int (-58896)); (W32.of_int (-29466)); (W32.of_int (-58538));
(W32.of_int (-30182)); (W32.of_int (-58172)); (W32.of_int (-30893));
(W32.of_int (-57798)); (W32.of_int (-31600)); (W32.of_int (-57414));
(W32.of_int (-32303)); (W32.of_int (-57022)); (W32.of_int (-33000));
(W32.of_int (-56621)); (W32.of_int (-33692)); (W32.of_int (-56212));
(W32.of_int (-34380)); (W32.of_int (-55794)); (W32.of_int (-35062));
(W32.of_int (-55368)); (W32.of_int (-35738)); (W32.of_int (-54934));
(W32.of_int (-36410)); (W32.of_int (-54491)); (W32.of_int (-37076));
(W32.of_int (-54040)); (W32.of_int (-37736)); (W32.of_int (-53581));
(W32.of_int (-38391)); (W32.of_int (-53114)); (W32.of_int (-39040));
(W32.of_int (-52639)); (W32.of_int (-39683)); (W32.of_int (-52156));
(W32.of_int (-40320)); (W32.of_int (-51665)); (W32.of_int (-40951));
(W32.of_int (-51166)); (W32.of_int (-41576)); (W32.of_int (-50660));
(W32.of_int (-42194)); (W32.of_int (-50146)); (W32.of_int (-42806));
(W32.of_int (-49624)); (W32.of_int (-43412)); (W32.of_int (-49095));
(W32.of_int (-44011)); (W32.of_int (-48559)); (W32.of_int (-44604));
(W32.of_int (-48015)); (W32.of_int (-45190)); (W32.of_int (-47464));
(W32.of_int (-45769)); (W32.of_int (-46906)); (W32.of_int (-46341));
(W32.of_int (-46341)); (W32.of_int (-46906)); (W32.of_int (-45769));
(W32.of_int (-47464)); (W32.of_int (-45190)); (W32.of_int (-48015));
(W32.of_int (-44604)); (W32.of_int (-48559)); (W32.of_int (-44011));
(W32.of_int (-49095)); (W32.of_int (-43412)); (W32.of_int (-49624));
(W32.of_int (-42806)); (W32.of_int (-50146)); (W32.of_int (-42194));
(W32.of_int (-50660)); (W32.of_int (-41576)); (W32.of_int (-51166));
(W32.of_int (-40951)); (W32.of_int (-51665)); (W32.of_int (-40320));
(W32.of_int (-52156)); (W32.of_int (-39683)); (W32.of_int (-52639));
(W32.of_int (-39040)); (W32.of_int (-53114)); (W32.of_int (-38391));
(W32.of_int (-53581)); (W32.of_int (-37736)); (W32.of_int (-54040));
(W32.of_int (-37076)); (W32.of_int (-54491)); (W32.of_int (-36410));
(W32.of_int (-54934)); (W32.of_int (-35738)); (W32.of_int (-55368));
(W32.of_int (-35062)); (W32.of_int (-55794)); (W32.of_int (-34380));
(W32.of_int (-56212)); (W32.of_int (-33692)); (W32.of_int (-56621));
(W32.of_int (-33000)); (W32.of_int (-57022)); (W32.of_int (-32303));
(W32.of_int (-57414)); (W32.of_int (-31600)); (W32.of_int (-57798));
(W32.of_int (-30893)); (W32.of_int (-58172)); (W32.of_int (-30182));
(W32.of_int (-58538)); (W32.of_int (-29466)); (W32.of_int (-58896));
(W32.of_int (-28745)); (W32.of_int (-59244)); (W32.of_int (-28020));
(W32.of_int (-59583)); (W32.of_int (-27291)); (W32.of_int (-59914));
(W32.of_int (-26558)); (W32.of_int (-60235)); (W32.of_int (-25821));
(W32.of_int (-60547)); (W32.of_int (-25080)); (W32.of_int (-60851));
(W32.of_int (-24335)); (W32.of_int (-61145)); (W32.of_int (-23586));
(W32.of_int (-61429)); (W32.of_int (-22834)); (W32.of_int (-61705));
(W32.of_int (-22078)); (W32.of_int (-61971)); (W32.of_int (-21320));
(W32.of_int (-62228)); (W32.of_int (-20557)); (W32.of_int (-62476));
(W32.of_int (-19792)); (W32.of_int (-62714)); (W32.of_int (-19024));
(W32.of_int (-62943)); (W32.of_int (-18253)); (W32.of_int (-63162));
(W32.of_int (-17479)); (W32.of_int (-63372)); (W32.of_int (-16703));
(W32.of_int (-63572)); (W32.of_int (-15924)); (W32.of_int (-63763));
(W32.of_int (-15143)); (W32.of_int (-63944)); (W32.of_int (-14359));
(W32.of_int (-64115)); (W32.of_int (-13573)); (W32.of_int (-64277));
(W32.of_int (-12785)); (W32.of_int (-64429)); (W32.of_int (-11996));
(W32.of_int (-64571)); (W32.of_int (-11204)); (W32.of_int (-64704));
(W32.of_int (-10411)); (W32.of_int (-64827)); (W32.of_int (-9616));
(W32.of_int (-64940)); (W32.of_int (-8820)); (W32.of_int (-65043));
(W32.of_int (-8022)); (W32.of_int (-65137)); (W32.of_int (-7224));
(W32.of_int (-65220)); (W32.of_int (-6424)); (W32.of_int (-65294));
(W32.of_int (-5623)); (W32.of_int (-65358)); (W32.of_int (-4821));
(W32.of_int (-65413)); (W32.of_int (-4019)); (W32.of_int (-65457));
(W32.of_int (-3216)); (W32.of_int (-65492)); (W32.of_int (-2412));
(W32.of_int (-65516)); (W32.of_int (-1608)); (W32.of_int (-65531));
(W32.of_int (-804))]).

abbrev jzetas_inv =
(BArray1024.of_list32
[(W32.of_int 20175); (W32.of_int (-8241)); (W32.of_int (-26554));
(W32.of_int (-31612)); (W32.of_int (-29003)); (W32.of_int 12979);
(W32.of_int (-17463)); (W32.of_int (-7947)); (W32.of_int 12831);
(W32.of_int (-25492)); (W32.of_int 14203); (W32.of_int 21126);
(W32.of_int (-9217)); (W32.of_int (-2931)); (W32.of_int 8099);
(W32.of_int (-13803)); (W32.of_int (-23078)); (W32.of_int (-15822));
(W32.of_int 27740); (W32.of_int 22820); (W32.of_int 16251);
(W32.of_int (-7655)); (W32.of_int 20206); (W32.of_int 994);
(W32.of_int 5823); (W32.of_int 9488); (W32.of_int (-23224));
(W32.of_int 1035); (W32.of_int (-8889)); (W32.of_int 21944);
(W32.of_int 27010); (W32.of_int (-21921)); (W32.of_int (-26934));
(W32.of_int 23751); (W32.of_int (-8908)); (W32.of_int (-10770));
(W32.of_int (-65)); (W32.of_int 3528); (W32.of_int 22805);
(W32.of_int 17737); (W32.of_int 4800); (W32.of_int 27298);
(W32.of_int (-1761)); (W32.of_int 10226); (W32.of_int 7729);
(W32.of_int 11242); (W32.of_int (-12069)); (W32.of_int (-13882));
(W32.of_int 22243); (W32.of_int 31368); (W32.of_int 2202);
(W32.of_int (-18282)); (W32.of_int 3304); (W32.of_int 8253);
(W32.of_int 26851); (W32.of_int (-17261)); (W32.of_int (-25636));
(W32.of_int 10865); (W32.of_int 26985); (W32.of_int (-10639));
(W32.of_int (-3808)); (W32.of_int 10170); (W32.of_int 25912);
(W32.of_int 29735); (W32.of_int 17374); (W32.of_int (-6080));
(W32.of_int (-21454)); (W32.of_int (-10672)); (W32.of_int 9939);
(W32.of_int 20316); (W32.of_int (-13283)); (W32.of_int 28190);
(W32.of_int 30274); (W32.of_int (-21422)); (W32.of_int 18166);
(W32.of_int (-7382)); (W32.of_int (-13642)); (W32.of_int (-5920));
(W32.of_int (-17494)); (W32.of_int (-17182)); (W32.of_int (-7742));
(W32.of_int (-23439)); (W32.of_int 16630); (W32.of_int 30332);
(W32.of_int 12882); (W32.of_int (-12380)); (W32.of_int 16160);
(W32.of_int (-28521)); (W32.of_int (-28254)); (W32.of_int 25921);
(W32.of_int 12543); (W32.of_int 21900); (W32.of_int 2648);
(W32.of_int 23016); (W32.of_int (-10971)); (W32.of_int (-1025));
(W32.of_int 16319); (W32.of_int 31332); (W32.of_int 1311);
(W32.of_int (-689)); (W32.of_int 19194); (W32.of_int 24162);
(W32.of_int (-14864)); (W32.of_int 8796); (W32.of_int 11808);
(W32.of_int (-7682)); (W32.of_int (-28847)); (W32.of_int 30317);
(W32.of_int 7401); (W32.of_int (-13633)); (W32.of_int (-30980));
(W32.of_int (-5764)); (W32.of_int (-13666)); (W32.of_int (-23475));
(W32.of_int 15739); (W32.of_int (-16588)); (W32.of_int 28772);
(W32.of_int 3529); (W32.of_int (-25555)); (W32.of_int (-2464));
(W32.of_int 9190); (W32.of_int 7374); (W32.of_int 21224);
(W32.of_int (-1657)); (W32.of_int 13857); (W32.of_int (-787));
(W32.of_int (-3350)); (W32.of_int 27989); (W32.of_int (-17671));
(W32.of_int (-9560)); (W32.of_int 21442); (W32.of_int (-30362));
(W32.of_int (-23844)); (W32.of_int 9874); (W32.of_int 18586);
(W32.of_int 9522); (W32.of_int (-5876)); (W32.of_int (-29439));
(W32.of_int (-2844)); (W32.of_int 16405); (W32.of_int (-5322));
(W32.of_int (-5913)); (W32.of_int 31064); (W32.of_int (-29563));
(W32.of_int (-7929)); (W32.of_int 14501); (W32.of_int (-12050));
(W32.of_int 18832); (W32.of_int 4127); (W32.of_int 16186);
(W32.of_int (-18731)); (W32.of_int (-21502)); (W32.of_int 27727);
(W32.of_int 10623); (W32.of_int (-11261)); (W32.of_int (-24985));
(W32.of_int 31327); (W32.of_int (-1160)); (W32.of_int (-28710));
(W32.of_int 14941); (W32.of_int (-15510)); (W32.of_int (-6759));
(W32.of_int (-22131)); (W32.of_int 29051); (W32.of_int (-16507));
(W32.of_int (-29068)); (W32.of_int (-9790)); (W32.of_int 5342);
(W32.of_int (-1806)); (W32.of_int 17631); (W32.of_int (-31352));
(W32.of_int 12442); (W32.of_int (-8311)); (W32.of_int (-1488));
(W32.of_int 27685); (W32.of_int (-3970)); (W32.of_int (-15546));
(W32.of_int (-835)); (W32.of_int (-4538)); (W32.of_int 29942);
(W32.of_int (-598)); (W32.of_int 19555); (W32.of_int 16267);
(W32.of_int (-17456)); (W32.of_int (-20353)); (W32.of_int (-19813));
(W32.of_int 9604); (W32.of_int 3761); (W32.of_int (-32114));
(W32.of_int (-12697)); (W32.of_int (-7814)); (W32.of_int (-11591));
(W32.of_int 9430); (W32.of_int (-10615)); (W32.of_int 11459);
(W32.of_int (-7597)); (W32.of_int (-27690)); (W32.of_int 19129);
(W32.of_int (-26533)); (W32.of_int 7941); (W32.of_int (-19616));
(W32.of_int 16608); (W32.of_int 23970); (W32.of_int (-30608));
(W32.of_int 2391); (W32.of_int 15130); (W32.of_int 19646);
(W32.of_int 21464); (W32.of_int (-7893)); (W32.of_int 8577);
(W32.of_int (-29643)); (W32.of_int 17941); (W32.of_int (-11782));
(W32.of_int 32076); (W32.of_int 19725); (W32.of_int 1296);
(W32.of_int (-18239)); (W32.of_int (-16446)); (W32.of_int 12296);
(W32.of_int (-16304)); (W32.of_int (-9383)); (W32.of_int 10049);
(W32.of_int 6789); (W32.of_int 22562); (W32.of_int (-25252));
(W32.of_int (-30820)); (W32.of_int 11361); (W32.of_int (-20143));
(W32.of_int 20035); (W32.of_int 29133); (W32.of_int 27527);
(W32.of_int (-28147)); (W32.of_int 29104); (W32.of_int (-22431));
(W32.of_int (-22935)); (W32.of_int (-10681)); (W32.of_int 19553);
(W32.of_int (-6241)); (W32.of_int 22946); (W32.of_int 16039);
(W32.of_int (-17599)); (W32.of_int (-21408)); (W32.of_int (-13744));
(W32.of_int (-32144)); (W32.of_int 8851); (W32.of_int (-22859));
(W32.of_int 30985); (W32.of_int (-9395)); (W32.of_int 31218);
(W32.of_int (-19064)); (W32.of_int (-20243)); (W32.of_int (-30746));
(W32.of_int (-22229)); (W32.of_int 16505); (W32.of_int (-26964));
(W32.of_int (-29720))]).

abbrev jzetas =
(BArray1024.of_list32
[(W32.of_int 0); (W32.of_int 26964); (W32.of_int (-16505));
(W32.of_int 22229); (W32.of_int 30746); (W32.of_int 20243);
(W32.of_int 19064); (W32.of_int (-31218)); (W32.of_int 9395);
(W32.of_int (-30985)); (W32.of_int 22859); (W32.of_int (-8851));
(W32.of_int 32144); (W32.of_int 13744); (W32.of_int 21408);
(W32.of_int 17599); (W32.of_int (-16039)); (W32.of_int (-22946));
(W32.of_int 6241); (W32.of_int (-19553)); (W32.of_int 10681);
(W32.of_int 22935); (W32.of_int 22431); (W32.of_int (-29104));
(W32.of_int 28147); (W32.of_int (-27527)); (W32.of_int (-29133));
(W32.of_int (-20035)); (W32.of_int 20143); (W32.of_int (-11361));
(W32.of_int 30820); (W32.of_int 25252); (W32.of_int (-22562));
(W32.of_int (-6789)); (W32.of_int (-10049)); (W32.of_int 9383);
(W32.of_int 16304); (W32.of_int (-12296)); (W32.of_int 16446);
(W32.of_int 18239); (W32.of_int (-1296)); (W32.of_int (-19725));
(W32.of_int (-32076)); (W32.of_int 11782); (W32.of_int (-17941));
(W32.of_int 29643); (W32.of_int (-8577)); (W32.of_int 7893);
(W32.of_int (-21464)); (W32.of_int (-19646)); (W32.of_int (-15130));
(W32.of_int (-2391)); (W32.of_int 30608); (W32.of_int (-23970));
(W32.of_int (-16608)); (W32.of_int 19616); (W32.of_int (-7941));
(W32.of_int 26533); (W32.of_int (-19129)); (W32.of_int 27690);
(W32.of_int 7597); (W32.of_int (-11459)); (W32.of_int 10615);
(W32.of_int (-9430)); (W32.of_int 11591); (W32.of_int 7814);
(W32.of_int 12697); (W32.of_int 32114); (W32.of_int (-3761));
(W32.of_int (-9604)); (W32.of_int 19813); (W32.of_int 20353);
(W32.of_int 17456); (W32.of_int (-16267)); (W32.of_int (-19555));
(W32.of_int 598); (W32.of_int (-29942)); (W32.of_int 4538); (W32.of_int 835);
(W32.of_int 15546); (W32.of_int 3970); (W32.of_int (-27685));
(W32.of_int 1488); (W32.of_int 8311); (W32.of_int (-12442));
(W32.of_int 31352); (W32.of_int (-17631)); (W32.of_int 1806);
(W32.of_int (-5342)); (W32.of_int 9790); (W32.of_int 29068);
(W32.of_int 16507); (W32.of_int (-29051)); (W32.of_int 22131);
(W32.of_int 6759); (W32.of_int 15510); (W32.of_int (-14941));
(W32.of_int 28710); (W32.of_int 1160); (W32.of_int (-31327));
(W32.of_int 24985); (W32.of_int 11261); (W32.of_int (-10623));
(W32.of_int (-27727)); (W32.of_int 21502); (W32.of_int 18731);
(W32.of_int (-16186)); (W32.of_int (-4127)); (W32.of_int (-18832));
(W32.of_int 12050); (W32.of_int (-14501)); (W32.of_int 7929);
(W32.of_int 29563); (W32.of_int (-31064)); (W32.of_int 5913);
(W32.of_int 5322); (W32.of_int (-16405)); (W32.of_int 2844);
(W32.of_int 29439); (W32.of_int 5876); (W32.of_int (-9522));
(W32.of_int (-18586)); (W32.of_int (-9874)); (W32.of_int 23844);
(W32.of_int 30362); (W32.of_int (-21442)); (W32.of_int 9560);
(W32.of_int 17671); (W32.of_int (-27989)); (W32.of_int 3350);
(W32.of_int 787); (W32.of_int (-13857)); (W32.of_int 1657);
(W32.of_int (-21224)); (W32.of_int (-7374)); (W32.of_int (-9190));
(W32.of_int 2464); (W32.of_int 25555); (W32.of_int (-3529));
(W32.of_int (-28772)); (W32.of_int 16588); (W32.of_int (-15739));
(W32.of_int 23475); (W32.of_int 13666); (W32.of_int 5764);
(W32.of_int 30980); (W32.of_int 13633); (W32.of_int (-7401));
(W32.of_int (-30317)); (W32.of_int 28847); (W32.of_int 7682);
(W32.of_int (-11808)); (W32.of_int (-8796)); (W32.of_int 14864);
(W32.of_int (-24162)); (W32.of_int (-19194)); (W32.of_int 689);
(W32.of_int (-1311)); (W32.of_int (-31332)); (W32.of_int (-16319));
(W32.of_int 1025); (W32.of_int 10971); (W32.of_int (-23016));
(W32.of_int (-2648)); (W32.of_int (-21900)); (W32.of_int (-12543));
(W32.of_int (-25921)); (W32.of_int 28254); (W32.of_int 28521);
(W32.of_int (-16160)); (W32.of_int 12380); (W32.of_int (-12882));
(W32.of_int (-30332)); (W32.of_int (-16630)); (W32.of_int 23439);
(W32.of_int 7742); (W32.of_int 17182); (W32.of_int 17494); (W32.of_int 5920);
(W32.of_int 13642); (W32.of_int 7382); (W32.of_int (-18166));
(W32.of_int 21422); (W32.of_int (-30274)); (W32.of_int (-28190));
(W32.of_int 13283); (W32.of_int (-20316)); (W32.of_int (-9939));
(W32.of_int 10672); (W32.of_int 21454); (W32.of_int 6080);
(W32.of_int (-17374)); (W32.of_int (-29735)); (W32.of_int (-25912));
(W32.of_int (-10170)); (W32.of_int 3808); (W32.of_int 10639);
(W32.of_int (-26985)); (W32.of_int (-10865)); (W32.of_int 25636);
(W32.of_int 17261); (W32.of_int (-26851)); (W32.of_int (-8253));
(W32.of_int (-3304)); (W32.of_int 18282); (W32.of_int (-2202));
(W32.of_int (-31368)); (W32.of_int (-22243)); (W32.of_int 13882);
(W32.of_int 12069); (W32.of_int (-11242)); (W32.of_int (-7729));
(W32.of_int (-10226)); (W32.of_int 1761); (W32.of_int (-27298));
(W32.of_int (-4800)); (W32.of_int (-17737)); (W32.of_int (-22805));
(W32.of_int (-3528)); (W32.of_int 65); (W32.of_int 10770); (W32.of_int 8908);
(W32.of_int (-23751)); (W32.of_int 26934); (W32.of_int 21921);
(W32.of_int (-27010)); (W32.of_int (-21944)); (W32.of_int 8889);
(W32.of_int (-1035)); (W32.of_int 23224); (W32.of_int (-9488));
(W32.of_int (-5823)); (W32.of_int (-994)); (W32.of_int (-20206));
(W32.of_int 7655); (W32.of_int (-16251)); (W32.of_int (-22820));
(W32.of_int (-27740)); (W32.of_int 15822); (W32.of_int 23078);
(W32.of_int 13803); (W32.of_int (-8099)); (W32.of_int 2931);
(W32.of_int 9217); (W32.of_int (-21126)); (W32.of_int (-14203));
(W32.of_int 25492); (W32.of_int (-12831)); (W32.of_int 7947);
(W32.of_int 17463); (W32.of_int (-12979)); (W32.of_int 29003);
(W32.of_int 31612); (W32.of_int 26554); (W32.of_int 8241);
(W32.of_int (-20175))]).

abbrev haetae_keccak1600_rc =
(BArray192.of_list64
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

module M = {
  proc _keccak_init_state (sp_0:BArray200.t) : BArray200.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 25))) {
      sp_0 <- (BArray200.set64 sp_0 (W64.to_uint i) (W64.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return sp_0;
  }
  proc _keccak_finalize (sp_0:BArray200.t, pos:W64.t, rate:W64.t, domain:W8.t) : 
  BArray200.t = {
    var lane:W64.t;
    var shift:W8.t;
    var t:W64.t;
    lane <- pos;
    lane <- (lane `>>` (W8.of_int 3));
    shift <- (truncateu8 pos);
    shift <- (shift `&` (W8.of_int 7));
    shift <- (shift `<<` (W8.of_int 3));
    t <- (zeroextu64 domain);
    t <- (t `<<` (shift `&` (W8.of_int 63)));
    sp_0 <-
    (BArray200.set64 sp_0 (W64.to_uint lane)
    ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
    lane <- rate;
    lane <- (lane `>>` (W8.of_int 3));
    lane <- (lane - (W64.of_int 1));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <-
    (BArray200.set64 sp_0 (W64.to_uint lane)
    ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
    return sp_0;
  }
  proc __keccakf1600_index (x:int, y:int) : int = {
    var r:int;
    r <- ((x %% 5) + (5 * (y %% 5)));
    return r;
  }
  proc __keccakf1600_rho_offset (i:int) : int = {
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while ((t < 24)) {
      if ((i = (x + (5 * y)))) {
        r <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
      } else {
        
      }
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- (t + 1);
    }
    return r;
  }
  proc __keccakf1600_rho (x:int, y:int) : int = {
    var r:int;
    var i:int;
    i <@ __keccakf1600_index (x, y);
    r <@ __keccakf1600_rho_offset (i);
    return r;
  }
  proc __rol_u64 (x:W64.t, i:int) : W64.t = {
    var  _0:bool;
    var  _1:bool;
    if ((i <> 0)) {
      ( _0,  _1, x) <- (ROL_64 x (W8.of_int i));
    } else {
      
    }
    return x;
  }
  proc __andn_u64 (a:W64.t, b:W64.t) : W64.t = {
    var t:W64.t;
    t <- ((invw a) `&` b);
    return t;
  }
  proc __keccak_theta_sum (a:BArray200.t) : BArray40.t = {
    var c:BArray40.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while ((x < 5)) {
      c <- (BArray40.set64 c x (BArray200.get64 a x));
      x <- (x + 1);
    }
    y <- 1;
    while ((y < 5)) {
      x <- 0;
      while ((x < 5)) {
        c <-
        (BArray40.set64 c x
        ((BArray40.get64 c x) `^` (BArray200.get64 a (x + (y * 5)))));
        x <- (x + 1);
      }
      y <- (y + 1);
    }
    return c;
  }
  proc __keccak_theta_rol (c:BArray40.t) : BArray40.t = {
    var aux:W64.t;
    var d:BArray40.t;
    var x:int;
    d <- witness;
    x <- 0;
    while ((x < 5)) {
      d <- (BArray40.set64 d x (BArray40.get64 c ((x + 1) %% 5)));
      aux <@ __rol_u64 ((BArray40.get64 d x), 1);
      d <- (BArray40.set64 d x aux);
      d <-
      (BArray40.set64 d x
      ((BArray40.get64 d x) `^` (BArray40.get64 c (((x - 1) + 5) %% 5))));
      x <- (x + 1);
    }
    return d;
  }
  proc __keccak_rol_sum (a:BArray200.t, d:BArray40.t, y:int) : BArray40.t = {
    var aux:W64.t;
    var b:BArray40.t;
    var x:int;
    var xp:int;
    var yp:int;
    var r:int;
    b <- witness;
    x <- 0;
    while ((x < 5)) {
      xp <- ((x + (3 * y)) %% 5);
      yp <- x;
      r <@ __keccakf1600_rho (xp, yp);
      b <- (BArray40.set64 b x (BArray200.get64 a (xp + (yp * 5))));
      b <-
      (BArray40.set64 b x ((BArray40.get64 b x) `^` (BArray40.get64 d xp)));
      aux <@ __rol_u64 ((BArray40.get64 b x), r);
      b <- (BArray40.set64 b x aux);
      x <- (x + 1);
    }
    return b;
  }
  proc __keccak_set_row (e:BArray200.t, b:BArray40.t, y:int) : BArray200.t = {
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    x <- 0;
    while ((x < 5)) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <@ __andn_u64 ((BArray40.get64 b x1), (BArray40.get64 b x2));
      t <- (t `^` (BArray40.get64 b x));
      e <- (BArray200.set64 e (x + (y * 5)) t);
      x <- (x + 1);
    }
    return e;
  }
  proc _keccak_pround (e:BArray200.t, a:BArray200.t) : BArray200.t = {
    var c:BArray40.t;
    var d:BArray40.t;
    var y:int;
    var b:BArray40.t;
    b <- witness;
    c <- witness;
    d <- witness;
    c <@ __keccak_theta_sum (a);
    d <@ __keccak_theta_rol (c);
    y <- 0;
    while ((y < 5)) {
      b <@ __keccak_rol_sum (a, d, y);
      e <@ __keccak_set_row (e, b, y);
      y <- (y + 1);
    }
    return e;
  }
  proc __keccakf1600_statepermute (a:BArray200.t) : BArray200.t = {
    var se:BArray200.t;
    var e:BArray200.t;
    var rcp:BArray192.t;
    var c:int;
    var rc:W64.t;
    e <- witness;
    rcp <- witness;
    se <- witness;
    e <- se;
    c <- 0;
    while ((c < 12)) {
      e <@ _keccak_pround (e, a);
      (a, e) <- (swap_ e a);
      rcp <- haetae_keccak1600_rc;
      rc <- (BArray192.get64 rcp (2 * c));
      e <- (BArray200.set64 e 0 ((BArray200.get64 e 0) `^` rc));
      a <@ _keccak_pround (a, e);
      (a, e) <- (swap_ e a);
      rcp <- haetae_keccak1600_rc;
      rc <- (BArray192.get64 rcp ((2 * c) + 1));
      a <- (BArray200.set64 a 0 ((BArray200.get64 a 0) `^` rc));
      c <- (c + 1);
    }
    return a;
  }
  proc _keccakf1600 (sp_0:BArray200.t) : BArray200.t = {
    
    sp_0 <@ __keccakf1600_statepermute (sp_0);
    return sp_0;
  }
  proc __poly_sample_squeeze128 (outp:BArray1024.t, outoff:W64.t,
                                 sp_0:BArray200.t) : BArray1024.t *
                                                     BArray200.t = {
    var idx:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var t:W64.t;
    var j:W64.t;
    var b:W8.t;
    idx <- outoff;
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    outp <- (protect_ptr outp ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 168))) {
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 8))) {
        b <- (truncateu8 t);
        outp <- (BArray1024.set8 outp (W64.to_uint idx) b);
        t <- (t `>>` (W8.of_int 8));
        idx <- (idx + (W64.of_int 1));
        j <- (j + (W64.of_int 1));
      }
      i <- (i + (W64.of_int 8));
    }
    return (outp, sp_0);
  }
  proc __poly_sample_squeeze256 (outp:BArray1024.t, outoff:W64.t,
                                 sp_0:BArray200.t) : BArray1024.t *
                                                     BArray200.t = {
    var idx:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var t:W64.t;
    var j:W64.t;
    var b:W8.t;
    idx <- outoff;
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    outp <- (protect_ptr outp ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 136))) {
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 8))) {
        b <- (truncateu8 t);
        outp <- (BArray1024.set8 outp (W64.to_uint idx) b);
        t <- (t `>>` (W8.of_int 8));
        idx <- (idx + (W64.of_int 1));
        j <- (j + (W64.of_int 1));
      }
      i <- (i + (W64.of_int 8));
    }
    return (outp, sp_0);
  }
  proc __poly_sample_mod3 (t:W32.t) : W32.t = {
    var r:W32.t;
    var u:W32.t;
    r <- t;
    r <- (r `>>` (W8.of_int 4));
    u <- t;
    u <- (u `&` (W32.of_int 15));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 2));
    r <- (r `&` (W32.of_int 3));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 2));
    r <- (r `&` (W32.of_int 3));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 2));
    r <- (r `&` (W32.of_int 3));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 1));
    u <- (u * (W32.of_int 3));
    r <- (r - u);
    return r;
  }
  proc __poly_sample_mod3_leq26 (t:W32.t) : W32.t = {
    var r:W32.t;
    var u:W32.t;
    r <- t;
    r <- (r `>>` (W8.of_int 4));
    u <- t;
    u <- (u `&` (W32.of_int 15));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 2));
    r <- (r `&` (W32.of_int 3));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 2));
    r <- (r `&` (W32.of_int 3));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 1));
    u <- (u * (W32.of_int 3));
    r <- (r - u);
    return r;
  }
  proc __poly_sample_mod3_leq8 (t:W32.t) : W32.t = {
    var r:W32.t;
    var u:W32.t;
    r <- t;
    r <- (r `>>` (W8.of_int 2));
    u <- t;
    u <- (u `&` (W32.of_int 3));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 2));
    r <- (r `&` (W32.of_int 3));
    r <- (r + u);
    u <- r;
    u <- (u `>>` (W8.of_int 1));
    u <- (u * (W32.of_int 3));
    r <- (r - u);
    return r;
  }
  proc __poly_uniform_consume (ap:BArray32768.t, base:W64.t, ctr:W64.t,
                               bp:BArray1024.t, buflen:W64.t) : BArray32768.t *
                                                                W64.t = {
    var pos:W64.t;
    var live:W64.t;
    var rem:W64.t;
    var byte:W8.t;
    var t:W32.t;
    var u:W32.t;
    var ms:W64.t;
    var b:bool;
    var idx:W64.t;
    pos <- (W64.of_int 0);
    live <- (W64.of_int 1);
    while ((live <> (W64.of_int 0))) {
      if (((W64.of_int 256) \ule ctr)) {
        live <- (W64.of_int 0);
      } else {
        rem <- buflen;
        rem <- (rem - pos);
        if ((rem \ult (W64.of_int 2))) {
          live <- (W64.of_int 0);
        } else {
          byte <- (BArray1024.get8 bp (W64.to_uint pos));
          t <- (zeroextu32 byte);
          pos <- (pos + (W64.of_int 1));
          byte <- (BArray1024.get8 bp (W64.to_uint pos));
          u <- (zeroextu32 byte);
          pos <- (pos + (W64.of_int 1));
          u <- (u `<<` (W8.of_int 8));
          t <- (t `|` u);
          (* Erased call to declassify *)
          ms <- (init_msf);
          t <- (protect_32 t ms);
          b <- (t \ult (W32.of_int 64513));
          if (b) {
            ms <- (update_msf b ms);
            idx <- base;
            idx <- (idx + ctr);
            ap <- (BArray32768.set32 ap (W64.to_uint idx) t);
            ctr <- (ctr + (W64.of_int 1));
          } else {
            ms <- (update_msf (! b) ms);
          }
        }
      }
    }
    return (ap, ctr);
  }
  proc __montgomery_reduce (a:W64.t) : W32.t = {
    var t32:W32.t;
    var t64:W64.t;
    t32 <- (truncateu32 a);
    t32 <- (t32 * (W32.of_int 940508161));
    t64 <- (sigextu64 t32);
    t64 <- (t64 * (W64.of_int 64513));
    a <- (a - t64);
    a <- (a `|>>` (W8.of_int 32));
    t32 <- (truncateu32 a);
    return t32;
  }
  proc __fqmul (a:W32.t, b:W32.t) : W32.t = {
    var r:W32.t;
    var ta:W64.t;
    var tb:W64.t;
    var t:W64.t;
    ta <- (sigextu64 a);
    tb <- (sigextu64 b);
    t <- (ta * tb);
    r <@ __montgomery_reduce (t);
    return r;
  }
  proc __freeze (a:W32.t) : W32.t = {
    var mask32:W32.t;
    var x:W64.t;
    var t:W64.t;
    var mask64:W64.t;
    x <- (sigextu64 a);
    t <- x;
    t <- (t * (W64.of_int 66575));
    t <- (t `|>>` (W8.of_int 32));
    t <- (t * (W64.of_int 64513));
    x <- (x - t);
    mask64 <- x;
    mask64 <- (mask64 `|>>` (W8.of_int 31));
    mask64 <- (mask64 `&` (W64.of_int 129026));
    x <- (x + mask64);
    mask64 <- x;
    mask64 <- (mask64 - (W64.of_int 64513));
    mask64 <- (mask64 `|>>` (W8.of_int 31));
    mask32 <- (truncateu32 mask64);
    mask32 <- (mask32 + (W32.of_int 1));
    mask32 <- (mask32 * (W32.of_int 64513));
    mask64 <- (zeroextu64 mask32);
    x <- (x - mask64);
    mask32 <- (truncateu32 x);
    return mask32;
  }
  proc _polyvec_ntt (xp:BArray8192.t, count:W64.t) : BArray8192.t = {
    var zetasp:BArray1024.t;
    var poly:W64.t;
    var base:W64.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W32.t;
    var j:W64.t;
    var cmp:W64.t;
    var idx:W64.t;
    var s:W32.t;
    var offset:W64.t;
    var idx2:W64.t;
    var coeff:W32.t;
    var t:W32.t;
    zetasp <- witness;
    zetasp <- jzetas;
    poly <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((poly \ult count)) {
      zetasctr <- (W64.of_int 0);
      len <- (W64.of_int 128);
      while (((W64.of_int 0) \ult len)) {
        start <- (W64.of_int 0);
        while ((start \ult (W64.of_int 256))) {
          zetasctr <- (zetasctr + (W64.of_int 1));
          zeta_0 <- (BArray1024.get32 zetasp (W64.to_uint zetasctr));
          j <- start;
          cmp <- start;
          cmp <- (cmp + len);
          while ((j \ult cmp)) {
            idx <- base;
            idx <- (idx + j);
            s <- (BArray8192.get32 xp (W64.to_uint idx));
            offset <- j;
            offset <- (offset + len);
            idx2 <- base;
            idx2 <- (idx2 + offset);
            coeff <- (BArray8192.get32 xp (W64.to_uint idx2));
            t <@ __fqmul (zeta_0, coeff);
            coeff <- s;
            coeff <- (coeff - t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx2) coeff);
            s <- (s + t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx) s);
            j <- (j + (W64.of_int 1));
          }
          start <- j;
          start <- (start + len);
        }
        len <- (len `>>` (W8.of_int 1));
      }
      base <- (base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return xp;
  }
  proc _polyvec_invntt (xp:BArray8192.t, count:W64.t) : BArray8192.t = {
    var zetasp:BArray1024.t;
    var poly:W64.t;
    var base:W64.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W32.t;
    var j:W64.t;
    var cmp:W64.t;
    var idx:W64.t;
    var t:W32.t;
    var offset:W64.t;
    var idx2:W64.t;
    var coeff:W32.t;
    var s:W32.t;
    zetasp <- witness;
    zetasp <- jzetas_inv;
    poly <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((poly \ult count)) {
      zetasctr <- (W64.of_int 0);
      len <- (W64.of_int 1);
      while ((len \ult (W64.of_int 256))) {
        start <- (W64.of_int 0);
        while ((start \ult (W64.of_int 256))) {
          zeta_0 <- (BArray1024.get32 zetasp (W64.to_uint zetasctr));
          zetasctr <- (zetasctr + (W64.of_int 1));
          j <- start;
          cmp <- start;
          cmp <- (cmp + len);
          while ((j \ult cmp)) {
            idx <- base;
            idx <- (idx + j);
            t <- (BArray8192.get32 xp (W64.to_uint idx));
            offset <- j;
            offset <- (offset + len);
            idx2 <- base;
            idx2 <- (idx2 + offset);
            coeff <- (BArray8192.get32 xp (W64.to_uint idx2));
            s <- t;
            s <- (s + coeff);
            xp <- (BArray8192.set32 xp (W64.to_uint idx) s);
            t <- (t - coeff);
            t <@ __fqmul (zeta_0, t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx2) t);
            j <- (j + (W64.of_int 1));
          }
          start <- j;
          start <- (start + len);
        }
        len <- (len `<<` (W8.of_int 1));
      }
      zeta_0 <- (BArray1024.get32 zetasp 255);
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        idx <- base;
        idx <- (idx + j);
        coeff <- (BArray8192.get32 xp (W64.to_uint idx));
        t <@ __fqmul (zeta_0, coeff);
        xp <- (BArray8192.set32 xp (W64.to_uint idx) t);
        j <- (j + (W64.of_int 1));
      }
      base <- (base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return xp;
  }
  proc _polymat_pointwise_acc (tp:BArray8192.t, mp:BArray32768.t,
                               vp:BArray8192.t, rows:W64.t, cols:W64.t) : 
  BArray8192.t = {
    var row:W64.t;
    var row_out:W64.t;
    var row_mat:W64.t;
    var j:W64.t;
    var oidx:W64.t;
    var col:W64.t;
    var col_off:W64.t;
    var midx:W64.t;
    var vidx:W64.t;
    var a:W32.t;
    var b:W32.t;
    var t:W32.t;
    var acc:W32.t;
    row <- (W64.of_int 0);
    row_out <- (W64.of_int 0);
    row_mat <- (W64.of_int 0);
    while ((row \ult rows)) {
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        oidx <- row_out;
        oidx <- (oidx + j);
        tp <- (BArray8192.set32 tp (W64.to_uint oidx) (W32.of_int 0));
        j <- (j + (W64.of_int 1));
      }
      col <- (W64.of_int 0);
      col_off <- (W64.of_int 0);
      while ((col \ult cols)) {
        j <- (W64.of_int 0);
        while ((j \ult (W64.of_int 256))) {
          midx <- row_mat;
          midx <- (midx + col_off);
          midx <- (midx + j);
          vidx <- col_off;
          vidx <- (vidx + j);
          oidx <- row_out;
          oidx <- (oidx + j);
          a <- (BArray32768.get32 mp (W64.to_uint midx));
          b <- (BArray8192.get32 vp (W64.to_uint vidx));
          t <@ __fqmul (a, b);
          acc <- (BArray8192.get32 tp (W64.to_uint oidx));
          acc <- (acc + t);
          tp <- (BArray8192.set32 tp (W64.to_uint oidx) acc);
          j <- (j + (W64.of_int 1));
        }
        col_off <- (col_off + (W64.of_int 256));
        col <- (col + (W64.of_int 1));
      }
      row_mat <- (row_mat + col_off);
      row_out <- (row_out + (W64.of_int 256));
      row <- (row + (W64.of_int 1));
    }
    return tp;
  }
  proc _pack_vk_m23 (vkp:BArray2080.t, bp:BArray8192.t, seedp:BArray32.t,
                     count:W64.t) : BArray2080.t = {
    var i:W64.t;
    var poly:W64.t;
    var coeff_base:W64.t;
    var off:W64.t;
    var base:W64.t;
    var a:W32.t;
    var out:W32.t;
    var next:W32.t;
    var part:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      vkp <-
      (BArray2080.set8 vkp (W64.to_uint i)
      (BArray32.get8 seedp (W64.to_uint i)));
      i <- (i + (W64.of_int 1));
    }
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    off <- (W64.of_int 32);
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 32))) {
        base <- coeff_base;
        base <- (base + ((W64.of_int 8) * i));
        a <- (BArray8192.get32 bp (W64.to_uint (base + (W64.of_int 0))));
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 0)))
        (truncateu8 a));
        out <- a;
        out <- (out `>>` (W8.of_int 8));
        out <- (out `&` (W32.of_int 127));
        next <- (BArray8192.get32 bp (W64.to_uint (base + (W64.of_int 1))));
        part <- next;
        part <- (part `&` (W32.of_int 1));
        part <- (part `<<` (W8.of_int 7));
        out <- (out `|` part);
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 1)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 1));
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 2)))
        (truncateu8 out));
        out <- a;
        out <- (out `>>` (W8.of_int 9));
        out <- (out `&` (W32.of_int 63));
        next <- (BArray8192.get32 bp (W64.to_uint (base + (W64.of_int 2))));
        part <- next;
        part <- (part `&` (W32.of_int 3));
        part <- (part `<<` (W8.of_int 6));
        out <- (out `|` part);
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 3)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 2));
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 4)))
        (truncateu8 out));
        out <- a;
        out <- (out `>>` (W8.of_int 10));
        out <- (out `&` (W32.of_int 31));
        next <- (BArray8192.get32 bp (W64.to_uint (base + (W64.of_int 3))));
        part <- next;
        part <- (part `&` (W32.of_int 7));
        part <- (part `<<` (W8.of_int 5));
        out <- (out `|` part);
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 5)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 3));
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 6)))
        (truncateu8 out));
        out <- a;
        out <- (out `>>` (W8.of_int 11));
        out <- (out `&` (W32.of_int 15));
        next <- (BArray8192.get32 bp (W64.to_uint (base + (W64.of_int 4))));
        part <- next;
        part <- (part `&` (W32.of_int 15));
        part <- (part `<<` (W8.of_int 4));
        out <- (out `|` part);
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 7)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 4));
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 8)))
        (truncateu8 out));
        out <- a;
        out <- (out `>>` (W8.of_int 12));
        out <- (out `&` (W32.of_int 7));
        next <- (BArray8192.get32 bp (W64.to_uint (base + (W64.of_int 5))));
        part <- next;
        part <- (part `&` (W32.of_int 31));
        part <- (part `<<` (W8.of_int 3));
        out <- (out `|` part);
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 9)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 5));
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 10)))
        (truncateu8 out));
        out <- a;
        out <- (out `>>` (W8.of_int 13));
        out <- (out `&` (W32.of_int 3));
        next <- (BArray8192.get32 bp (W64.to_uint (base + (W64.of_int 6))));
        part <- next;
        part <- (part `&` (W32.of_int 63));
        part <- (part `<<` (W8.of_int 2));
        out <- (out `|` part);
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 11)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 6));
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 12)))
        (truncateu8 out));
        out <- a;
        out <- (out `>>` (W8.of_int 14));
        out <- (out `&` (W32.of_int 1));
        next <- (BArray8192.get32 bp (W64.to_uint (base + (W64.of_int 7))));
        part <- next;
        part <- (part `&` (W32.of_int 127));
        part <- (part `<<` (W8.of_int 1));
        out <- (out `|` part);
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 13)))
        (truncateu8 out));
        out <- next;
        out <- (out `>>` (W8.of_int 7));
        vkp <-
        (BArray2080.set8 vkp (W64.to_uint (off + (W64.of_int 14)))
        (truncateu8 out));
        i <- (i + (W64.of_int 1));
        off <- (off + (W64.of_int 15));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return vkp;
  }
  proc _pack_vec_eta_to (outp:BArray2752.t, vp:BArray8192.t, out_off:W64.t,
                         count:W64.t) : BArray2752.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var base:W64.t;
    var t:W32.t;
    var out:W32.t;
    var part:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    pos <- out_off;
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 64))) {
        base <- coeff_base;
        base <- (base + ((W64.of_int 4) * i));
        t <- (W32.of_int 1);
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 0)))));
        t <- (t `&` (W32.of_int 255));
        out <- t;
        t <- (W32.of_int 1);
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 1)))));
        t <- (t `&` (W32.of_int 255));
        part <- t;
        part <- (part `<<` (W8.of_int 2));
        out <- (out `|` part);
        t <- (W32.of_int 1);
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 2)))));
        t <- (t `&` (W32.of_int 255));
        part <- t;
        part <- (part `<<` (W8.of_int 4));
        out <- (out `|` part);
        t <- (W32.of_int 1);
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 3)))));
        t <- (t `&` (W32.of_int 255));
        part <- t;
        part <- (part `<<` (W8.of_int 6));
        out <- (out `|` part);
        outp <- (BArray2752.set8 outp (W64.to_uint pos) (truncateu8 out));
        i <- (i + (W64.of_int 1));
        pos <- (pos + (W64.of_int 1));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return outp;
  }
  proc _pack_vec2_eta_to (outp:BArray2752.t, vp:BArray8192.t, out_off:W64.t,
                          count:W64.t) : BArray2752.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var base:W64.t;
    var t:W32.t;
    var out:W32.t;
    var part:W32.t;
    var carry:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    pos <- out_off;
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 32))) {
        base <- coeff_base;
        base <- (base + ((W64.of_int 8) * i));
        t <- (W32.of_int (2 * 1));
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 0)))));
        t <- (t `&` (W32.of_int 255));
        out <- t;
        t <- (W32.of_int (2 * 1));
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 1)))));
        t <- (t `&` (W32.of_int 255));
        part <- t;
        part <- (part `<<` (W8.of_int 3));
        out <- (out `|` part);
        t <- (W32.of_int (2 * 1));
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 2)))));
        t <- (t `&` (W32.of_int 255));
        carry <- t;
        part <- t;
        part <- (part `<<` (W8.of_int 6));
        out <- (out `|` part);
        outp <-
        (BArray2752.set8 outp (W64.to_uint (pos + (W64.of_int 0)))
        (truncateu8 out));
        out <- carry;
        out <- (out `>>` (W8.of_int 2));
        t <- (W32.of_int (2 * 1));
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 3)))));
        t <- (t `&` (W32.of_int 255));
        part <- t;
        part <- (part `<<` (W8.of_int 1));
        out <- (out `|` part);
        t <- (W32.of_int (2 * 1));
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 4)))));
        t <- (t `&` (W32.of_int 255));
        part <- t;
        part <- (part `<<` (W8.of_int 4));
        out <- (out `|` part);
        t <- (W32.of_int (2 * 1));
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 5)))));
        t <- (t `&` (W32.of_int 255));
        carry <- t;
        part <- t;
        part <- (part `<<` (W8.of_int 7));
        out <- (out `|` part);
        outp <-
        (BArray2752.set8 outp (W64.to_uint (pos + (W64.of_int 1)))
        (truncateu8 out));
        out <- carry;
        out <- (out `>>` (W8.of_int 1));
        t <- (W32.of_int (2 * 1));
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 6)))));
        t <- (t `&` (W32.of_int 255));
        part <- t;
        part <- (part `<<` (W8.of_int 2));
        out <- (out `|` part);
        t <- (W32.of_int (2 * 1));
        t <-
        (t - (BArray8192.get32 vp (W64.to_uint (base + (W64.of_int 7)))));
        t <- (t `&` (W32.of_int 255));
        part <- t;
        part <- (part `<<` (W8.of_int 5));
        out <- (out `|` part);
        outp <-
        (BArray2752.set8 outp (W64.to_uint (pos + (W64.of_int 2)))
        (truncateu8 out));
        i <- (i + (W64.of_int 1));
        pos <- (pos + (W64.of_int 3));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return outp;
  }
  proc _pack_sk_m23 (skp:BArray2752.t, vkp:BArray2080.t, s0p:BArray8192.t,
                     s1p:BArray8192.t, keyp:BArray32.t, vkbytes:W64.t,
                     mcount:W64.t, kcount:W64.t) : BArray2752.t = {
    var i:W64.t;
    var off:W64.t;
    var step:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult vkbytes)) {
      skp <-
      (BArray2752.set8 skp (W64.to_uint i)
      (BArray2080.get8 vkp (W64.to_uint i)));
      i <- (i + (W64.of_int 1));
    }
    off <- vkbytes;
    skp <@ _pack_vec_eta_to (skp, s0p, off, mcount);
    step <- mcount;
    step <- (step * (W64.of_int 64));
    off <- (off + step);
    skp <@ _pack_vec2_eta_to (skp, s1p, off, kcount);
    step <- kcount;
    step <- (step * (W64.of_int 96));
    off <- (off + step);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      step <- off;
      step <- (step + i);
      skp <-
      (BArray2752.set8 skp (W64.to_uint step)
      (BArray32.get8 keyp (W64.to_uint i)));
      i <- (i + (W64.of_int 1));
    }
    return skp;
  }
  proc __sk_singular_value_minmax (a:W32.t, b:W32.t) : W32.t * W32.t = {
    var ab:W32.t;
    var c:W32.t;
    var t:W32.t;
    ab <- b;
    ab <- (ab `^` a);
    c <- b;
    c <- (c - a);
    t <- c;
    t <- (t `^` b);
    t <- (t `&` ab);
    c <- (c `^` t);
    c <- (c `|>>` (W8.of_int 31));
    c <- (c `&` ab);
    a <- (a `^` c);
    b <- (b `^` c);
    return (a, b);
  }
  proc __sk_singular_value_mulrnd16 (x:W32.t, y:W32.t) : W32.t = {
    var out:W32.t;
    var xx:W64.t;
    var yy:W64.t;
    var r:W64.t;
    xx <- (sigextu64 x);
    yy <- (sigextu64 y);
    r <- (xx * yy);
    r <- (r + (W64.of_int 32768));
    r <- (r `|>>` (W8.of_int 16));
    out <- (truncateu32 r);
    return out;
  }
  proc _sk_singular_value_accumulate_fft_sqabs (sump:BArray1024.t,
                                                inputp:BArray2048.t) : 
  BArray1024.t = {
    var i:W64.t;
    var idx:W64.t;
    var real:W32.t;
    var imag:W32.t;
    var sq:W32.t;
    var acc:W32.t;
    i <- (W64.of_int 0);
    idx <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      real <- (BArray2048.get32 inputp (W64.to_uint idx));
      idx <- (idx + (W64.of_int 1));
      imag <- (BArray2048.get32 inputp (W64.to_uint idx));
      idx <- (idx + (W64.of_int 1));
      sq <@ __sk_singular_value_mulrnd16 (real, real);
      acc <@ __sk_singular_value_mulrnd16 (imag, imag);
      sq <- (sq + acc);
      acc <- (BArray1024.get32 sump (W64.to_uint i));
      acc <- (acc + sq);
      sump <- (BArray1024.set32 sump (W64.to_uint i) acc);
      i <- (i + (W64.of_int 1));
    }
    return sump;
  }
  proc _keypair_finalize_m23 (bp:BArray8192.t, s2p:BArray8192.t,
                              ap:BArray8192.t, count:W64.t) : BArray8192.t *
                                                              BArray8192.t = {
    var i:W64.t;
    var b:W32.t;
    var s2:W32.t;
    var a:W32.t;
    var low:W32.t;
    var tmp:W32.t;
    var high:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      b <- (BArray8192.get32 bp (W64.to_uint i));
      s2 <- (BArray8192.get32 s2p (W64.to_uint i));
      a <- (BArray8192.get32 ap (W64.to_uint i));
      b <- (b + s2);
      b <- (b + a);
      b <@ __freeze (b);
      low <- b;
      low <- (low `&` (W32.of_int 1));
      tmp <- b;
      tmp <- (tmp `|>>` (W8.of_int 1));
      tmp <- (tmp `&` low);
      tmp <- (tmp `<<` (W8.of_int 1));
      low <- (low - tmp);
      high <- b;
      high <- (high - low);
      high <- (high `|>>` (W8.of_int 1));
      bp <- (BArray8192.set32 bp (W64.to_uint i) high);
      s2 <- (s2 - low);
      s2p <- (BArray8192.set32 s2p (W64.to_uint i) s2);
      i <- (i + (W64.of_int 1));
    }
    return (bp, s2p);
  }
  proc __fft_mulrnd16 (x:W32.t, y:W32.t) : W32.t = {
    var out:W32.t;
    var xx:W64.t;
    var yy:W64.t;
    var r:W64.t;
    xx <- (sigextu64 x);
    yy <- (sigextu64 y);
    r <- (xx * yy);
    r <- (r + (W64.of_int 32768));
    r <- (r `|>>` (W8.of_int 16));
    out <- (truncateu32 r);
    return out;
  }
  proc _fft_init_and_bitrev (rp:BArray2048.t, xp:BArray1024.t,
                             rootsp:BArray2048.t, brvp:BArray512.t) : 
  BArray2048.t = {
    var i:W64.t;
    var inv:W16.t;
    var ridx:W64.t;
    var ms:W64.t;
    var c:W32.t;
    var idx:W64.t;
    var root:W32.t;
    var val:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      inv <- (BArray512.get16 brvp (W64.to_uint i));
      ridx <- (zeroextu64 inv);
      (* Erased call to declassify *)
      ms <- (init_msf);
      ridx <- (protect_64 ridx ms);
      ridx <- (ridx `<<` (W8.of_int 1));
      c <- (BArray1024.get32 xp (W64.to_uint i));
      idx <- i;
      idx <- (idx `<<` (W8.of_int 1));
      root <- (BArray2048.get32 rootsp (W64.to_uint idx));
      val <- c;
      val <- (val * root);
      rp <- (BArray2048.set32 rp (W64.to_uint ridx) val);
      idx <- (idx + (W64.of_int 1));
      ridx <- (ridx + (W64.of_int 1));
      root <- (BArray2048.get32 rootsp (W64.to_uint idx));
      val <- c;
      val <- (val * root);
      rp <- (BArray2048.set32 rp (W64.to_uint ridx) val);
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc _fft_butterfly (datap:BArray2048.t, rootsp:BArray2048.t, even:W64.t,
                       odd:W64.t, twid:W64.t) : BArray2048.t = {
    var eidx:W64.t;
    var oidx:W64.t;
    var tidx:W64.t;
    var ureal:W32.t;
    var idx:W64.t;
    var uimag:W32.t;
    var oreal:W32.t;
    var oimag:W32.t;
    var rreal:W32.t;
    var rimag:W32.t;
    var ar:W32.t;
    var ai:W32.t;
    var treal:W32.t;
    var br:W32.t;
    var bi:W32.t;
    var timag:W32.t;
    var out:W32.t;
    eidx <- even;
    eidx <- (eidx `<<` (W8.of_int 1));
    oidx <- odd;
    oidx <- (oidx `<<` (W8.of_int 1));
    tidx <- twid;
    tidx <- (tidx `<<` (W8.of_int 1));
    ureal <- (BArray2048.get32 datap (W64.to_uint eidx));
    idx <- eidx;
    idx <- (idx + (W64.of_int 1));
    uimag <- (BArray2048.get32 datap (W64.to_uint idx));
    oreal <- (BArray2048.get32 datap (W64.to_uint oidx));
    idx <- oidx;
    idx <- (idx + (W64.of_int 1));
    oimag <- (BArray2048.get32 datap (W64.to_uint idx));
    rreal <- (BArray2048.get32 rootsp (W64.to_uint tidx));
    idx <- tidx;
    idx <- (idx + (W64.of_int 1));
    rimag <- (BArray2048.get32 rootsp (W64.to_uint idx));
    ar <@ __fft_mulrnd16 (rreal, oreal);
    ai <@ __fft_mulrnd16 (rimag, oimag);
    treal <- ar;
    treal <- (treal - ai);
    br <@ __fft_mulrnd16 (rreal, oimag);
    bi <@ __fft_mulrnd16 (rimag, oreal);
    timag <- br;
    timag <- (timag + bi);
    out <- ureal;
    out <- (out + treal);
    datap <- (BArray2048.set32 datap (W64.to_uint eidx) out);
    idx <- eidx;
    idx <- (idx + (W64.of_int 1));
    out <- uimag;
    out <- (out + timag);
    datap <- (BArray2048.set32 datap (W64.to_uint idx) out);
    out <- ureal;
    out <- (out - treal);
    datap <- (BArray2048.set32 datap (W64.to_uint oidx) out);
    idx <- oidx;
    idx <- (idx + (W64.of_int 1));
    out <- uimag;
    out <- (out - timag);
    datap <- (BArray2048.set32 datap (W64.to_uint idx) out);
    return datap;
  }
  proc _fft_full (datap:BArray2048.t, rootsp:BArray2048.t) : BArray2048.t = {
    var r:W64.t;
    var m:W64.t;
    var md2:W64.t;
    var stride:W64.t;
    var n:W64.t;
    var k:W64.t;
    var even:W64.t;
    var odd:W64.t;
    var twid:W64.t;
    var ms:W64.t;
    r <- (W64.of_int 1);
    m <- (W64.of_int 2);
    md2 <- (W64.of_int 1);
    stride <- (W64.of_int 256);
    while ((r \ule (W64.of_int 8))) {
      n <- (W64.of_int 0);
      while ((n \ult (W64.of_int 256))) {
        k <- (W64.of_int 0);
        while ((k \ult md2)) {
          even <- n;
          even <- (even + k);
          odd <- even;
          odd <- (odd + md2);
          twid <- k;
          twid <- (twid * stride);
          (* Erased call to spill *)
          datap <@ _fft_butterfly (datap, rootsp, even, odd, twid);
          (* Erased call to unspill *)
          (* Erased call to declassify *)
          (* Erased call to declassify *)
          (* Erased call to declassify *)
          (* Erased call to declassify *)
          (* Erased call to declassify *)
          (* Erased call to declassify *)
          ms <- (init_msf);
          datap <- (protect_ptr datap ms);
          rootsp <- (protect_ptr rootsp ms);
          r <- (protect_64 r ms);
          m <- (protect_64 m ms);
          md2 <- (protect_64 md2 ms);
          n <- (protect_64 n ms);
          k <- (protect_64 k ms);
          stride <- (protect_64 stride ms);
          k <- (k + (W64.of_int 1));
        }
        n <- (n + m);
      }
      r <- (r + (W64.of_int 1));
      m <- (m `<<` (W8.of_int 1));
      md2 <- (md2 `<<` (W8.of_int 1));
      stride <- (stride `>>` (W8.of_int 1));
    }
    return datap;
  }
  proc _singular_clear_sum (sump:BArray1024.t) : BArray1024.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      sump <- (BArray1024.set32 sump (W64.to_uint i) (W32.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return sump;
  }
  proc _singular_finish_typed (sump:BArray1024.t, best_count:int, tau:int,
                               rem:int) : W64.t = {
    var r:W64.t;
    var i:W64.t;
    var x:W32.t;
    var bestm:BArray20.t;
    var j:W64.t;
    var y:W32.t;
    var min:W32.t;
    var tmp:W32.t;
    var res_0:W32.t;
    var fac:W32.t;
    var notfac:W32.t;
    bestm <- witness;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int best_count))) {
      x <- (BArray1024.get32 sump (W64.to_uint i));
      bestm <- (BArray20.set32 bestm (W64.to_uint i) x);
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int best_count);
    while ((i \ult (W64.of_int 256))) {
      x <- (BArray1024.get32 sump (W64.to_uint i));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int best_count))) {
        y <- (BArray20.get32 bestm (W64.to_uint j));
        (x, y) <@ __sk_singular_value_minmax (x, y);
        bestm <- (BArray20.set32 bestm (W64.to_uint j) y);
        j <- (j + (W64.of_int 1));
      }
      i <- (i + (W64.of_int 1));
    }
    min <- (BArray20.get32 bestm 0);
    i <- (W64.of_int 1);
    while ((i \ult (W64.of_int best_count))) {
      tmp <- (BArray20.get32 bestm (W64.to_uint i));
      (min, tmp) <@ __sk_singular_value_minmax (min, tmp);
      i <- (i + (W64.of_int 1));
    }
    res_0 <- (W32.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int best_count))) {
      tmp <- (BArray20.get32 bestm (W64.to_uint i));
      fac <- min;
      fac <- (fac - tmp);
      fac <- (fac `|>>` (W8.of_int 31));
      notfac <- fac;
      notfac <- (notfac `^` (W32.of_int 4294967295));
      notfac <- (notfac `&` (W32.of_int rem));
      fac <- (fac `&` (W32.of_int tau));
      fac <- (fac `^` notfac);
      tmp <- (tmp + (W32.of_int 66048));
      tmp <- (tmp `|>>` (W8.of_int 10));
      tmp <- (tmp * fac);
      res_0 <- (res_0 + tmp);
      i <- (i + (W64.of_int 1));
    }
    r <- (sigextu64 res_0);
    r <- (r + (W64.of_int 32));
    r <- (r `|>>` (W8.of_int 6));
    return r;
  }
  proc _singular_full (s1p:BArray8192.t, s2p:BArray8192.t, mcount:int,
                       kcount:int, best_count:int, tau:int, rem:int) : 
  W64.t = {
    var r:W64.t;
    var input:BArray2048.t;
    var inputp:BArray2048.t;
    var sum:BArray1024.t;
    var sump:BArray1024.t;
    var rootsp:BArray2048.t;
    var brvp:BArray512.t;
    var i:W64.t;
    var base:W64.t;
    var xp:BArray1024.t;
    var ms:W64.t;
    brvp <- witness;
    input <- witness;
    inputp <- witness;
    rootsp <- witness;
    sum <- witness;
    sump <- witness;
    xp <- witness;
    inputp <- input;
    sump <- sum;
    rootsp <- jfft_roots;
    brvp <- jfft_brv8;
    sump <@ _singular_clear_sum (sump);
    i <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((i \ult (W64.of_int mcount))) {
      xp <- (SBArray8192_1024.get_sub32 s1p (W64.to_uint base));
      (* Erased call to spill *)
      inputp <@ _fft_init_and_bitrev (inputp, xp, rootsp, brvp);
      inputp <@ _fft_full (inputp, rootsp);
      sump <@ _sk_singular_value_accumulate_fft_sqabs (sump, inputp);
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      s1p <- (protect_ptr s1p ms);
      s2p <- (protect_ptr s2p ms);
      inputp <- (protect_ptr inputp ms);
      sump <- (protect_ptr sump ms);
      rootsp <- (protect_ptr rootsp ms);
      brvp <- (protect_ptr brvp ms);
      i <- (protect_64 i ms);
      base <- (protect_64 base ms);
      base <- (base + (W64.of_int 256));
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((i \ult (W64.of_int kcount))) {
      xp <- (SBArray8192_1024.get_sub32 s2p (W64.to_uint base));
      (* Erased call to spill *)
      inputp <@ _fft_init_and_bitrev (inputp, xp, rootsp, brvp);
      inputp <@ _fft_full (inputp, rootsp);
      sump <@ _sk_singular_value_accumulate_fft_sqabs (sump, inputp);
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      s1p <- (protect_ptr s1p ms);
      s2p <- (protect_ptr s2p ms);
      inputp <- (protect_ptr inputp ms);
      sump <- (protect_ptr sump ms);
      rootsp <- (protect_ptr rootsp ms);
      brvp <- (protect_ptr brvp ms);
      i <- (protect_64 i ms);
      base <- (protect_64 base ms);
      base <- (base + (W64.of_int 256));
      i <- (i + (W64.of_int 1));
    }
    r <@ _singular_finish_typed (sump, best_count, tau, rem);
    return r;
  }
  proc __kp_shake128_init_seedbuf (sp_0:BArray200.t, seedp:BArray128.t,
                                   seedoff:W64.t, nonce:W64.t) : BArray200.t = {
    var n:W64.t;
    var pos:W64.t;
    var idx:W64.t;
    var b:W8.t;
    var lane:W64.t;
    var t:W64.t;
    var shift:W8.t;
    var k:int;
    sp_0 <@ _keccak_init_state (sp_0);
    n <- nonce;
    pos <- (W64.of_int 0);
    while ((pos \ult (W64.of_int 32))) {
      idx <- seedoff;
      idx <- (idx + pos);
      b <- (BArray128.get8 seedp (W64.to_uint idx));
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      pos <- (pos + (W64.of_int 1));
    }
    k <- 0;
    while ((k < 2)) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (truncateu8 n);
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      n <- (n `>>` (W8.of_int 8));
      pos <- (pos + (W64.of_int 1));
      k <- (k + 1);
    }
    t <- (W64.of_int 31);
    t <- (t `<<` (W8.of_int 16));
    sp_0 <- (BArray200.set64 sp_0 4 ((BArray200.get64 sp_0 4) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 20 ((BArray200.get64 sp_0 20) `^` t));
    return sp_0;
  }
  proc __kp_shake256_init_seedbuf (sp_0:BArray200.t, seedp:BArray128.t,
                                   seedoff:W64.t, nonce:W64.t) : BArray200.t = {
    var n:W64.t;
    var pos:W64.t;
    var idx:W64.t;
    var b:W8.t;
    var lane:W64.t;
    var t:W64.t;
    var shift:W8.t;
    var k:int;
    sp_0 <@ _keccak_init_state (sp_0);
    n <- nonce;
    pos <- (W64.of_int 0);
    while ((pos \ult (W64.of_int 64))) {
      idx <- seedoff;
      idx <- (idx + pos);
      b <- (BArray128.get8 seedp (W64.to_uint idx));
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      pos <- (pos + (W64.of_int 1));
    }
    k <- 0;
    while ((k < 2)) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (truncateu8 n);
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      n <- (n `>>` (W8.of_int 8));
      pos <- (pos + (W64.of_int 1));
      k <- (k + 1);
    }
    t <- (W64.of_int 31);
    t <- (t `<<` (W8.of_int 16));
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 16 ((BArray200.get64 sp_0 16) `^` t));
    return sp_0;
  }
  proc __kp_poly_uniform_consume_2048 (ap:BArray8192.t, base:W64.t,
                                       ctr:W64.t, bp:BArray1024.t,
                                       buflen:W64.t) : BArray8192.t * W64.t = {
    var pos:W64.t;
    var live:W64.t;
    var rem:W64.t;
    var byte:W8.t;
    var t:W32.t;
    var u:W32.t;
    var ms:W64.t;
    var idx:W64.t;
    pos <- (W64.of_int 0);
    live <- (W64.of_int 1);
    while ((live <> (W64.of_int 0))) {
      if (((W64.of_int 256) \ule ctr)) {
        live <- (W64.of_int 0);
      } else {
        rem <- buflen;
        rem <- (rem - pos);
        if ((rem \ult (W64.of_int 2))) {
          live <- (W64.of_int 0);
        } else {
          byte <- (BArray1024.get8 bp (W64.to_uint pos));
          t <- (zeroextu32 byte);
          pos <- (pos + (W64.of_int 1));
          byte <- (BArray1024.get8 bp (W64.to_uint pos));
          u <- (zeroextu32 byte);
          pos <- (pos + (W64.of_int 1));
          u <- (u `<<` (W8.of_int 8));
          t <- (t `|` u);
          (* Erased call to declassify *)
          ms <- (init_msf);
          t <- (protect_32 t ms);
          if ((t \ult (W32.of_int 64513))) {
            idx <- base;
            idx <- (idx + ctr);
            ap <- (BArray8192.set32 ap (W64.to_uint idx) t);
            ctr <- (ctr + (W64.of_int 1));
          } else {
            
          }
        }
      }
    }
    return (ap, ctr);
  }
  proc __kp_poly_uniform_eta_consume_2048 (ap:BArray8192.t, base:W64.t,
                                           ctr:W64.t, bp:BArray1024.t,
                                           buflen:W64.t) : BArray8192.t *
                                                           W64.t = {
    var pos:W64.t;
    var live:W64.t;
    var byte:W8.t;
    var t:W32.t;
    var ms:W64.t;
    var r:W32.t;
    var idx:W64.t;
    pos <- (W64.of_int 0);
    live <- (W64.of_int 1);
    while ((live <> (W64.of_int 0))) {
      if (((W64.of_int 256) \ule ctr)) {
        live <- (W64.of_int 0);
      } else {
        if ((pos \ult buflen)) {
          byte <- (BArray1024.get8 bp (W64.to_uint pos));
          t <- (zeroextu32 byte);
          pos <- (pos + (W64.of_int 1));
          (* Erased call to declassify *)
          ms <- (init_msf);
          t <- (protect_32 t ms);
          if ((t \ult (W32.of_int 243))) {
            r <@ __poly_sample_mod3 (t);
            idx <- base;
            idx <- (idx + ctr);
            ap <- (BArray8192.set32 ap (W64.to_uint idx) r);
            ctr <- (ctr + (W64.of_int 1));
            if ((ctr \ult (W64.of_int 256))) {
              t <- (t * (W32.of_int 171));
              t <- (t `>>` (W8.of_int 9));
              r <@ __poly_sample_mod3 (t);
              idx <- base;
              idx <- (idx + ctr);
              ap <- (BArray8192.set32 ap (W64.to_uint idx) r);
              ctr <- (ctr + (W64.of_int 1));
            } else {
              
            }
            if ((ctr \ult (W64.of_int 256))) {
              t <- (t * (W32.of_int 171));
              t <- (t `>>` (W8.of_int 9));
              r <@ __poly_sample_mod3_leq26 (t);
              idx <- base;
              idx <- (idx + ctr);
              ap <- (BArray8192.set32 ap (W64.to_uint idx) r);
              ctr <- (ctr + (W64.of_int 1));
            } else {
              
            }
            if ((ctr \ult (W64.of_int 256))) {
              t <- (t * (W32.of_int 171));
              t <- (t `>>` (W8.of_int 9));
              r <@ __poly_sample_mod3_leq8 (t);
              idx <- base;
              idx <- (idx + ctr);
              ap <- (BArray8192.set32 ap (W64.to_uint idx) r);
              ctr <- (ctr + (W64.of_int 1));
            } else {
              
            }
            if ((ctr \ult (W64.of_int 256))) {
              t <- (t * (W32.of_int 171));
              t <- (t `>>` (W8.of_int 9));
              r <- t;
              r <- (r `>>` (W8.of_int 1));
              r <- (r * (W32.of_int 3));
              t <- (t - r);
              idx <- base;
              idx <- (idx + ctr);
              ap <- (BArray8192.set32 ap (W64.to_uint idx) t);
              ctr <- (ctr + (W64.of_int 1));
            } else {
              
            }
          } else {
            
          }
        } else {
          live <- (W64.of_int 0);
        }
      }
    }
    return (ap, ctr);
  }
  proc _kp_poly_uniform_at_seedbuf_8192 (ap:BArray32768.t, base:W64.t,
                                         seedp:BArray128.t, seedoff:W64.t,
                                         nonce:W64.t) : BArray32768.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var buf:BArray1024.t;
    var bufp:BArray1024.t;
    var off:W64.t;
    var ctr:W64.t;
    var buflen:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var idx:W64.t;
    var b:W8.t;
    buf <- witness;
    bufp <- witness;
    sp_0 <- witness;
    state <- witness;
    sp_0 <- state;
    bufp <- buf;
    sp_0 <@ __kp_shake128_init_seedbuf (sp_0, seedp, seedoff, nonce);
    off <- (W64.of_int 0);
    (* Erased call to spill *)
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 168);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 336);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 504);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    (* Erased call to unspill *)
    ctr <- (W64.of_int 0);
    buflen <- (W64.of_int 672);
    (ap, ctr) <@ __poly_uniform_consume (ap, base, ctr, bufp, buflen);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    ap <- (protect_ptr ap ms);
    bufp <- (protect_ptr bufp ms);
    base <- (protect_64 base ms);
    ctr <- (protect_64 ctr ms);
    while ((ctr \ult (W64.of_int 256))) {
      off <- buflen;
      off <- (off `&` (W64.of_int 1));
      i <- (W64.of_int 0);
      while ((i \ult off)) {
        idx <- buflen;
        idx <- (idx - off);
        idx <- (idx + i);
        b <- (BArray1024.get8 bufp (W64.to_uint idx));
        bufp <- (BArray1024.set8 bufp (W64.to_uint i) b);
        i <- (i + (W64.of_int 1));
      }
      (* Erased call to spill *)
      (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
      (* Erased call to declassify *)
      (* Erased call to unspill *)
      buflen <- (W64.of_int 168);
      buflen <- (buflen + off);
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      ap <- (protect_ptr ap ms);
      bufp <- (protect_ptr bufp ms);
      base <- (protect_64 base ms);
      ctr <- (protect_64 ctr ms);
      buflen <- (protect_64 buflen ms);
      (ap, ctr) <@ __poly_uniform_consume (ap, base, ctr, bufp, buflen);
      (* Erased call to declassify *)
      ms <- (init_msf);
      ap <- (protect_ptr ap ms);
      bufp <- (protect_ptr bufp ms);
      ctr <- (protect_64 ctr ms);
    }
    return ap;
  }
  proc _kp_poly_uniform_at_seedbuf_2048 (ap:BArray8192.t, base:W64.t,
                                         seedp:BArray128.t, seedoff:W64.t,
                                         nonce:W64.t) : BArray8192.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var buf:BArray1024.t;
    var bufp:BArray1024.t;
    var off:W64.t;
    var ctr:W64.t;
    var buflen:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var idx:W64.t;
    var b:W8.t;
    buf <- witness;
    bufp <- witness;
    sp_0 <- witness;
    state <- witness;
    sp_0 <- state;
    bufp <- buf;
    sp_0 <@ __kp_shake128_init_seedbuf (sp_0, seedp, seedoff, nonce);
    off <- (W64.of_int 0);
    (* Erased call to spill *)
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 168);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 336);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 504);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    (* Erased call to unspill *)
    ctr <- (W64.of_int 0);
    buflen <- (W64.of_int 672);
    (ap, ctr) <@ __kp_poly_uniform_consume_2048 (ap, base, ctr, bufp,
    buflen);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    ap <- (protect_ptr ap ms);
    bufp <- (protect_ptr bufp ms);
    base <- (protect_64 base ms);
    ctr <- (protect_64 ctr ms);
    while ((ctr \ult (W64.of_int 256))) {
      off <- buflen;
      off <- (off `&` (W64.of_int 1));
      i <- (W64.of_int 0);
      while ((i \ult off)) {
        idx <- buflen;
        idx <- (idx - off);
        idx <- (idx + i);
        b <- (BArray1024.get8 bufp (W64.to_uint idx));
        bufp <- (BArray1024.set8 bufp (W64.to_uint i) b);
        i <- (i + (W64.of_int 1));
      }
      (* Erased call to spill *)
      (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
      (* Erased call to declassify *)
      (* Erased call to unspill *)
      buflen <- (W64.of_int 168);
      buflen <- (buflen + off);
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      ap <- (protect_ptr ap ms);
      bufp <- (protect_ptr bufp ms);
      base <- (protect_64 base ms);
      ctr <- (protect_64 ctr ms);
      buflen <- (protect_64 buflen ms);
      (ap, ctr) <@ __kp_poly_uniform_consume_2048 (ap, base, ctr, bufp,
      buflen);
      (* Erased call to declassify *)
      ms <- (init_msf);
      ap <- (protect_ptr ap ms);
      bufp <- (protect_ptr bufp ms);
      ctr <- (protect_64 ctr ms);
    }
    return ap;
  }
  proc _kp_poly_uniform_eta_at_seedbuf_2048 (ap:BArray8192.t, base:W64.t,
                                             seedp:BArray128.t,
                                             seedoff:W64.t, nonce:W64.t) : 
  BArray8192.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var buf:BArray1024.t;
    var bufp:BArray1024.t;
    var off:W64.t;
    var ctr:W64.t;
    var buflen:W64.t;
    var ms:W64.t;
    buf <- witness;
    bufp <- witness;
    sp_0 <- witness;
    state <- witness;
    sp_0 <- state;
    bufp <- buf;
    sp_0 <@ __kp_shake256_init_seedbuf (sp_0, seedp, seedoff, nonce);
    off <- (W64.of_int 0);
    (* Erased call to spill *)
    (bufp, sp_0) <@ __poly_sample_squeeze256 (bufp, off, sp_0);
    (* Erased call to declassify *)
    (* Erased call to unspill *)
    ctr <- (W64.of_int 0);
    buflen <- (W64.of_int 136);
    (ap, ctr) <@ __kp_poly_uniform_eta_consume_2048 (ap, base, ctr, bufp,
    buflen);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    ap <- (protect_ptr ap ms);
    bufp <- (protect_ptr bufp ms);
    base <- (protect_64 base ms);
    ctr <- (protect_64 ctr ms);
    while ((ctr \ult (W64.of_int 256))) {
      (* Erased call to spill *)
      (bufp, sp_0) <@ __poly_sample_squeeze256 (bufp, off, sp_0);
      (* Erased call to declassify *)
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      ap <- (protect_ptr ap ms);
      bufp <- (protect_ptr bufp ms);
      base <- (protect_64 base ms);
      ctr <- (protect_64 ctr ms);
      buflen <- (protect_64 buflen ms);
      (ap, ctr) <@ __kp_poly_uniform_eta_consume_2048 (ap, base, ctr, 
      bufp, buflen);
      (* Erased call to declassify *)
      ms <- (init_msf);
      ap <- (protect_ptr ap ms);
      bufp <- (protect_ptr bufp ms);
      ctr <- (protect_64 ctr ms);
    }
    return ap;
  }
  proc _kp_polymatkm_expand_matA (matp:BArray32768.t, seedp:BArray128.t,
                                  rows:W64.t, cols:W64.t) : BArray32768.t = {
    var seedoff:W64.t;
    var i:W64.t;
    var rowbase:W64.t;
    var j:W64.t;
    var nonce:W64.t;
    var base:W64.t;
    var ms:W64.t;
    seedoff <- (W64.of_int 0);
    i <- (W64.of_int 0);
    rowbase <- (W64.of_int 0);
    while ((i \ult rows)) {
      j <- (W64.of_int 0);
      while ((j \ult cols)) {
        nonce <- i;
        nonce <- (nonce `<<` (W8.of_int 8));
        nonce <- (nonce + j);
        base <- rowbase;
        base <- (base + j);
        base <- (base * (W64.of_int 256));
        (* Erased call to spill *)
        matp <@ _kp_poly_uniform_at_seedbuf_8192 (matp, base, seedp, 
        seedoff, nonce);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        matp <- (protect_ptr matp ms);
        seedp <- (protect_ptr seedp ms);
        rows <- (protect_64 rows ms);
        cols <- (protect_64 cols ms);
        i <- (protect_64 i ms);
        j <- (protect_64 j ms);
        rowbase <- (protect_64 rowbase ms);
        seedoff <- (protect_64 seedoff ms);
        j <- (j + (W64.of_int 1));
      }
      rowbase <- (rowbase + cols);
      i <- (i + (W64.of_int 1));
    }
    return matp;
  }
  proc _kp_polyveck_expand_vecA (vp:BArray8192.t, seedp:BArray128.t, k:W64.t,
                                 m:W64.t) : BArray8192.t = {
    var seedoff:W64.t;
    var nonce:W64.t;
    var i:W64.t;
    var base:W64.t;
    var ms:W64.t;
    seedoff <- (W64.of_int 0);
    nonce <- k;
    nonce <- (nonce `<<` (W8.of_int 8));
    nonce <- (nonce + m);
    i <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((i \ult k)) {
      (* Erased call to spill *)
      vp <@ _kp_poly_uniform_at_seedbuf_2048 (vp, base, seedp, seedoff,
      nonce);
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      vp <- (protect_ptr vp ms);
      seedp <- (protect_ptr seedp ms);
      k <- (protect_64 k ms);
      m <- (protect_64 m ms);
      i <- (protect_64 i ms);
      base <- (protect_64 base ms);
      nonce <- (protect_64 nonce ms);
      seedoff <- (protect_64 seedoff ms);
      i <- (i + (W64.of_int 1));
      base <- (base + (W64.of_int 256));
      nonce <- (nonce + (W64.of_int 1));
    }
    return vp;
  }
  proc _kp_polyvec_expand_eta (vp:BArray8192.t, seedp:BArray128.t,
                               nonce:W64.t, count:W64.t) : BArray8192.t = {
    var seedoff:W64.t;
    var i:W64.t;
    var base:W64.t;
    var ms:W64.t;
    seedoff <- (W64.of_int 32);
    i <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((i \ult count)) {
      (* Erased call to spill *)
      vp <@ _kp_poly_uniform_eta_at_seedbuf_2048 (vp, base, seedp, seedoff,
      nonce);
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      vp <- (protect_ptr vp ms);
      seedp <- (protect_ptr seedp ms);
      nonce <- (protect_64 nonce ms);
      count <- (protect_64 count ms);
      i <- (protect_64 i ms);
      base <- (protect_64 base ms);
      seedoff <- (protect_64 seedoff ms);
      i <- (i + (W64.of_int 1));
      base <- (base + (W64.of_int 256));
      nonce <- (nonce + (W64.of_int 1));
    }
    return vp;
  }
  proc _kp_expand_seedbuf (outp:BArray128.t, seedp:BArray32.t) : BArray128.t = {
    var s:BArray200.t;
    var sp_0:BArray200.t;
    var pos:W64.t;
    var b:W8.t;
    var lane:W64.t;
    var t:W64.t;
    var shift:W8.t;
    var rate:W64.t;
    var domain:W8.t;
    var idx:W64.t;
    s <- witness;
    sp_0 <- witness;
    sp_0 <- s;
    sp_0 <@ _keccak_init_state (sp_0);
    pos <- (W64.of_int 0);
    while ((pos \ult (W64.of_int 32))) {
      b <- (BArray32.get8 seedp (W64.to_uint pos));
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      pos <- (pos + (W64.of_int 1));
    }
    rate <- (W64.of_int 136);
    domain <- (W8.of_int 31);
    sp_0 <@ _keccak_finalize (sp_0, pos, rate, domain);
    sp_0 <@ _keccakf1600 (sp_0);
    idx <- (W64.of_int 0);
    while ((idx \ult (W64.of_int 128))) {
      lane <- idx;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      shift <- (truncateu8 idx);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `>>` (shift `&` (W8.of_int 63)));
      b <- (truncateu8 t);
      outp <- (BArray128.set8 outp (W64.to_uint idx) b);
      idx <- (idx + (W64.of_int 1));
    }
    return outp;
  }
  proc _kp_copy_vec (rp:BArray8192.t, ap:BArray8192.t, count:W64.t) : 
  BArray8192.t = {
    var i:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      a <- (BArray8192.get32 ap (W64.to_uint i));
      rp <- (BArray8192.set32 rp (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc _kp_m23_matrix (bp:BArray8192.t, s1hatp:BArray8192.t,
                       ap:BArray32768.t, s1p:BArray8192.t, rows:W64.t,
                       cols:W64.t) : BArray8192.t * BArray8192.t = {
    var count:W64.t;
    var ms:W64.t;
    count <- cols;
    count <- (count * (W64.of_int 256));
    s1hatp <@ _kp_copy_vec (s1hatp, s1p, count);
    (* Erased call to spill *)
    s1hatp <@ _polyvec_ntt (s1hatp, cols);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    ap <- (protect_ptr ap ms);
    s1hatp <- (protect_ptr s1hatp ms);
    rows <- (protect_64 rows ms);
    cols <- (protect_64 cols ms);
    bp <@ _polymat_pointwise_acc (bp, ap, s1hatp, rows, cols);
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    rows <- (protect_64 rows ms);
    bp <@ _polyvec_invntt (bp, rows);
    return (bp, s1hatp);
  }
  proc _keypair_full_m23 (vkp:BArray2080.t, skp:BArray2752.t,
                          seedp:BArray32.t, k:int, m:int, vkbytes:int,
                          best_count:int, tau:int, rem:int,
                          singular_bound:int) : BArray2080.t * BArray2752.t = {
    var seedbuf:BArray128.t;
    var seedbufp:BArray128.t;
    var mat:BArray32768.t;
    var matp:BArray32768.t;
    var avec:BArray8192.t;
    var ap:BArray8192.t;
    var bvec:BArray8192.t;
    var bp:BArray8192.t;
    var s1:BArray8192.t;
    var s1p:BArray8192.t;
    var s1hat:BArray8192.t;
    var s1hatp:BArray8192.t;
    var s2:BArray8192.t;
    var s2p:BArray8192.t;
    var kr:W64.t;
    var mr:W64.t;
    var vkbr:W64.t;
    var counter:W64.t;
    var reject:W64.t;
    var nonce:W64.t;
    var count:W64.t;
    var ms:W64.t;
    var sv:W64.t;
    var bound:W64.t;
    var rhop:BArray32.t;
    var keyp:BArray32.t;
    ap <- witness;
    avec <- witness;
    bp <- witness;
    bvec <- witness;
    keyp <- witness;
    mat <- witness;
    matp <- witness;
    rhop <- witness;
    s1 <- witness;
    s1hat <- witness;
    s1hatp <- witness;
    s1p <- witness;
    s2 <- witness;
    s2p <- witness;
    seedbuf <- witness;
    seedbufp <- witness;
    seedbufp <- seedbuf;
    matp <- mat;
    ap <- avec;
    bp <- bvec;
    s1p <- s1;
    s1hatp <- s1hat;
    s2p <- s2;
    kr <- (W64.of_int k);
    mr <- (W64.of_int m);
    vkbr <- (W64.of_int vkbytes);
    seedbufp <@ _kp_expand_seedbuf (seedbufp, seedp);
    matp <@ _kp_polymatkm_expand_matA (matp, seedbufp, kr, mr);
    ap <@ _kp_polyveck_expand_vecA (ap, seedbufp, kr, mr);
    counter <- (W64.of_int 0);
    reject <- (W64.of_int 1);
    while ((reject <> (W64.of_int 0))) {
      s1p <@ _kp_polyvec_expand_eta (s1p, seedbufp, counter, mr);
      nonce <- counter;
      nonce <- (nonce + mr);
      s2p <@ _kp_polyvec_expand_eta (s2p, seedbufp, nonce, kr);
      counter <- (counter + mr);
      counter <- (counter + kr);
      (* Erased call to spill *)
      (bp, s1hatp) <@ _kp_m23_matrix (bp, s1hatp, matp, s1p, kr, mr);
      (* Erased call to unspill *)
      count <- kr;
      count <- (count * (W64.of_int 256));
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      bp <- (protect_ptr bp ms);
      s1p <- (protect_ptr s1p ms);
      s2p <- (protect_ptr s2p ms);
      ap <- (protect_ptr ap ms);
      seedbufp <- (protect_ptr seedbufp ms);
      kr <- (protect_64 kr ms);
      mr <- (protect_64 mr ms);
      count <- (protect_64 count ms);
      (bp, s2p) <@ _keypair_finalize_m23 (bp, s2p, ap, count);
      sv <@ _singular_full (s1p, s2p, m, k, best_count, tau, rem);
      bound <- (W64.of_int singular_bound);
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      sv <- (protect_64 sv ms);
      bound <- (protect_64 bound ms);
      reject <- (W64.of_int 0);
      if ((bound \ult sv)) {
        reject <- (W64.of_int 1);
      } else {
        
      }
    }
    rhop <- (SBArray128_32.get_sub8 seedbufp 0);
    keyp <- (SBArray128_32.get_sub8 seedbufp 96);
    vkp <@ _pack_vk_m23 (vkp, bp, rhop, kr);
    skp <@ _pack_sk_m23 (skp, vkp, s1p, s2p, keyp, vkbr, mr, kr);
    return (vkp, skp);
  }
  proc crypto_sign_keypair_internal_mode2_jazz (vkp:BArray2080.t,
                                                skp:BArray2752.t,
                                                seedp:BArray32.t) : BArray2080.t *
                                                                    BArray2752.t = {
    var ms:W64.t;
    ms <- (init_msf);
    vkp <- (protect_ptr vkp ms);
    skp <- (protect_ptr skp ms);
    seedp <- (protect_ptr seedp ms);
    (vkp, skp) <@ _keypair_full_m23 (vkp, skp, seedp, 2, 3, 992, 5, 58, 24,
    611098);
    return (vkp, skp);
  }
}.
