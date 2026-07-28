require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array5 Array24 Array25 Array32 Array128 Array256 Array512 Array1024 Array2048
Array8192 WArray192 WArray512 WArray1024 WArray2048 BArray32 BArray40
BArray128 BArray192 BArray200 BArray512 BArray1024 BArray2048 BArray8192
BArray32768.

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
}.
