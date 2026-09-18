require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array1 Array2 Array24 Array26 Array76 Array166 Array256 Array512 Array8192
WArray192 WArray304 WArray1024 WArray1328 BArray4 BArray8 BArray16 BArray26
BArray192 BArray304 BArray1024 BArray1328 BArray4096 BArray8192.

abbrev jcdt83_lo =
(BArray1328.of_list64
[(W64.of_int 767145465612017192); (W64.of_int 5708348702329189102);
(W64.of_int (-2986515139374512380)); (W64.of_int 7315992374869995997);
(W64.of_int (-7240595365343461296)); (W64.of_int 195392804384423549);
(W64.of_int 956154643040125894); (W64.of_int (-387090023418055461));
(W64.of_int (-6839973910006153600)); (W64.of_int 1752582669294548863);
(W64.of_int 4800866410357959959); (W64.of_int 3667394071068326311);
(W64.of_int 7998665258853332362); (W64.of_int 1039285826929998432);
(W64.of_int (-5325172712904727316)); (W64.of_int 8302908906926177525);
(W64.of_int 8594781109006420459); (W64.of_int (-5174631349969467793));
(W64.of_int 8655299069842505098); (W64.of_int (-5152057033357634684));
(W64.of_int (-7176303742971548487)); (W64.of_int (-4736152177093509389));
(W64.of_int 9014672416777812641); (W64.of_int 4984359074700584923);
(W64.of_int (-2887029340802828403)); (W64.of_int (-7587158779559040837));
(W64.of_int (-3226889267410948733)); (W64.of_int 2938417944103238712);
(W64.of_int (-2279529697979260704)); (W64.of_int 7021364755983520008);
(W64.of_int (-5699981999439543809)); (W64.of_int (-70422136106126370));
(W64.of_int 4972332497587472585); (W64.of_int (-1005689185452603130));
(W64.of_int (-6353529195586080244)); (W64.of_int 418384427087521389);
(W64.of_int (-9048179565493353424)); (W64.of_int 5860820516995035126);
(W64.of_int 6144759436214999286); (W64.of_int 2057362318352304828);
(W64.of_int (-1833664629943763904)); (W64.of_int (-5686588886910490621));
(W64.of_int 5484949054085740288); (W64.of_int 8266722527040612711);
(W64.of_int (-1736797318333312100)); (W64.of_int (-7619591592559817454));
(W64.of_int (-5653300277827871264)); (W64.of_int (-2805408635628270210));
(W64.of_int 4201673510770952224); (W64.of_int (-5542802630767400586));
(W64.of_int (-963011482571663333)); (W64.of_int (-7391284510404850280));
(W64.of_int 6273169357352979088); (W64.of_int 456876313255139270);
(W64.of_int (-4092082967717326062)); (W64.of_int 1621190494596410906);
(W64.of_int (-2053365783733785617)); (W64.of_int (-6670276636412627550));
(W64.of_int 7115633661535853623); (W64.of_int (-3128754293651494253));
(W64.of_int 6935088653178559021); (W64.of_int 3249567803139592707);
(W64.of_int 3228497872348613985); (W64.of_int 2608497649573788682);
(W64.of_int (-5557320224091228199)); (W64.of_int 6459840567858685922);
(W64.of_int (-9221884450999136146)); (W64.of_int 8703981739283037248);
(W64.of_int (-8798104171703783439)); (W64.of_int (-2620674995057133332));
(W64.of_int (-6683477291279709549)); (W64.of_int (-202686826310768826));
(W64.of_int 203645829219293199); (W64.of_int (-4039817201464381253));
(W64.of_int 6618745965193433548); (W64.of_int (-3860679526618670689));
(W64.of_int 2071704274388800110); (W64.of_int 6471675482471026258);
(W64.of_int (-8724390486189509312)); (W64.of_int (-6332167634226479284));
(W64.of_int (-4578558332206810384)); (W64.of_int (-3298093711129306011));
(W64.of_int (-2366758840984369973)); (W64.of_int (-1692001402250280346));
(W64.of_int (-1205041686108142602)); (W64.of_int (-854982138418773943));
(W64.of_int (-604316758675095801)); (W64.of_int (-425523836596219738));
(W64.of_int (-298492804824911630)); (W64.of_int (-208590077685954889));
(W64.of_int (-145211944389320022)); (W64.of_int (-100706867223975277));
(W64.of_int (-69576574077182978)); (W64.of_int (-47886531750657860));
(W64.of_int (-32832905617300018)); (W64.of_int (-22425909576001919));
(W64.of_int (-15259309166283028)); (W64.of_int (-10343392321865658));
(W64.of_int (-6984474311914934)); (W64.of_int (-4698360669985171));
(W64.of_int (-3148474636774176)); (W64.of_int (-2101815542697524));
(W64.of_int (-1397748079304948)); (W64.of_int (-925981864506689));
(W64.of_int (-611103417999386)); (W64.of_int (-401758429195526));
(W64.of_int (-263119325522126)); (W64.of_int (-171663273123127));
(W64.of_int (-111567669955921)); (W64.of_int (-72232911965015));
(W64.of_int (-46587256485616)); (W64.of_int (-29931872023758));
(W64.of_int (-19157324087377)); (W64.of_int (-12214326882085));
(W64.of_int (-7757780197058)); (W64.of_int (-4908379885196));
(W64.of_int (-3093649914360)); (W64.of_int (-1942388117830));
(W64.of_int (-1214876870458)); (W64.of_int (-756936566813));
(W64.of_int (-469804590101)); (W64.of_int (-290472590512));
(W64.of_int (-178905127292)); (W64.of_int (-109766482441));
(W64.of_int (-67088124190)); (W64.of_int (-40846054556));
(W64.of_int (-24773237568)); (W64.of_int (-14967292570));
(W64.of_int (-9008058511)); (W64.of_int (-5400652945));
(W64.of_int (-3225433705)); (W64.of_int (-1918917990));
(W64.of_int (-1137236592)); (W64.of_int (-671384067));
(W64.of_int (-394835975)); (W64.of_int (-231306359));
(W64.of_int (-134984312)); (W64.of_int (-78469989));
(W64.of_int (-45441029)); (W64.of_int (-26212999)); (W64.of_int (-15062913));
(W64.of_int (-8622330)); (W64.of_int (-4916583)); (W64.of_int (-2792704));
(W64.of_int (-1580188)); (W64.of_int (-890665)); (W64.of_int (-500082));
(W64.of_int (-279697)); (W64.of_int (-155831)); (W64.of_int (-86484));
(W64.of_int (-47811)); (W64.of_int (-26328)); (W64.of_int (-14441));
(W64.of_int (-7889)); (W64.of_int (-4292)); (W64.of_int (-2325));
(W64.of_int (-1253)); (W64.of_int (-672)); (W64.of_int (-358));
(W64.of_int (-189)); (W64.of_int (-98)); (W64.of_int (-50));
(W64.of_int (-25)); (W64.of_int (-12)); (W64.of_int (-5)); (W64.of_int (-2))]
).

abbrev jcdt83_hi =
(BArray304.of_list32
[(W32.of_int 25509); (W32.of_int 50968); (W32.of_int 76278);
(W32.of_int 101343); (W32.of_int 126067); (W32.of_int 150361);
(W32.of_int 174138); (W32.of_int 197318); (W32.of_int 219830);
(W32.of_int 241607); (W32.of_int 262590); (W32.of_int 282730);
(W32.of_int 301985); (W32.of_int 320323); (W32.of_int 337718);
(W32.of_int 354156); (W32.of_int 369628); (W32.of_int 384134);
(W32.of_int 397682); (W32.of_int 410285); (W32.of_int 421964);
(W32.of_int 432744); (W32.of_int 442656); (W32.of_int 451734);
(W32.of_int 460015); (W32.of_int 467541); (W32.of_int 474353);
(W32.of_int 480496); (W32.of_int 486012); (W32.of_int 490948);
(W32.of_int 495346); (W32.of_int 499250); (W32.of_int 502703);
(W32.of_int 505743); (W32.of_int 508411); (W32.of_int 510743);
(W32.of_int 512772); (W32.of_int 514532); (W32.of_int 516052);
(W32.of_int 517360); (W32.of_int 518480); (W32.of_int 519437);
(W32.of_int 520251); (W32.of_int 520940); (W32.of_int 521521);
(W32.of_int 522010); (W32.of_int 522419); (W32.of_int 522760);
(W32.of_int 523044); (W32.of_int 523278); (W32.of_int 523471);
(W32.of_int 523630); (W32.of_int 523760); (W32.of_int 523866);
(W32.of_int 523951); (W32.of_int 524021); (W32.of_int 524076);
(W32.of_int 524121); (W32.of_int 524157); (W32.of_int 524185);
(W32.of_int 524208); (W32.of_int 524226); (W32.of_int 524240);
(W32.of_int 524251); (W32.of_int 524259); (W32.of_int 524266);
(W32.of_int 524271); (W32.of_int 524275); (W32.of_int 524278);
(W32.of_int 524280); (W32.of_int 524282); (W32.of_int 524283);
(W32.of_int 524285); (W32.of_int 524285); (W32.of_int 524286);
(W32.of_int 524286)]).

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

module M = {
  proc __mul48 (a:W64.t, b:W64.t) : W64.t * W64.t = {
    var lo:W64.t;
    var hi:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var top:W64.t;
    var mask:W64.t;
    rax <- a;
    (rdx, rax) <- (mulu_64 rax b);
    lo <- rax;
    hi <- rdx;
    hi <- (hi `<<` (W8.of_int 16));
    top <- lo;
    top <- (top `>>` (W8.of_int 48));
    hi <- (hi `^` top);
    mask <- (W64.of_int 281474976710655);
    lo <- (lo `&` mask);
    return (lo, hi);
  }
  proc __fixpoint_square_regs (x0:W64.t, x1:W64.t) : W64.t * W64.t = {
    var r0:W64.t;
    var r1:W64.t;
    var mask:W64.t;
    var lo:W64.t;
    var hi:W64.t;
    var tmp:W64.t;
    mask <- (W64.of_int 281474976710655);
    (lo, hi) <@ __mul48 (x0, x0);
    r0 <- lo;
    r0 <- (r0 `>>` (W8.of_int 48));
    r0 <- (r0 + hi);
    (lo, hi) <@ __mul48 (x0, x1);
    lo <- (lo `<<` (W8.of_int 1));
    r0 <- (r0 + lo);
    r1 <- hi;
    r1 <- (r1 `<<` (W8.of_int 1));
    r0 <- (r0 `>>` (W8.of_int 28));
    tmp <- r1;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    r1 <- (r1 `>>` (W8.of_int 28));
    tmp <- x1;
    (hi, tmp) <- (mulu_64 tmp x1);
    lo <- tmp;
    tmp <- lo;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    lo <- (lo `>>` (W8.of_int 28));
    hi <- (hi `<<` (W8.of_int 36));
    lo <- (lo + hi);
    r1 <- (r1 + lo);
    tmp <- r0;
    tmp <- (tmp `>>` (W8.of_int 48));
    r1 <- (r1 + tmp);
    r0 <- (r0 `&` mask);
    return (r0, r1);
  }
  proc _fixpoint_square (rp:BArray16.t, xp:BArray16.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var r0:W64.t;
    var r1:W64.t;
    x0 <- (BArray16.get64 xp 0);
    x1 <- (BArray16.get64 xp 1);
    (r0, r1) <@ __fixpoint_square_regs (x0, x1);
    rp <- (BArray16.set64 rp 0 r0);
    rp <- (BArray16.set64 rp 1 r1);
    return rp;
  }
  proc _sample_gauss83 (rand_lo:W64.t, rand_hi:W32.t) : W64.t = {
    var r:W64.t;
    var hip:BArray304.t;
    var lop:BArray1328.t;
    var rndhi:W64.t;
    var i:W64.t;
    var c:W32.t;
    var hi:W64.t;
    var lo:W64.t;
    var borrow:bool;
    var  _0:bool;
    var  _1:bool;
    hip <- witness;
    lop <- witness;
    hip <- jcdt83_hi;
    lop <- jcdt83_lo;
    rndhi <- (zeroextu64 rand_hi);
    i <- (W64.of_int 0);
    r <- (W64.of_int 0);
    while ((i \ult (W64.of_int 76))) {
      c <- (BArray304.get32 hip (W64.to_uint i));
      hi <- (zeroextu64 c);
      lo <- (BArray1328.get64 lop (W64.to_uint i));
      (borrow, lo) <- (sbb_64 lo rand_lo false);
      ( _0, hi) <- (sbb_64 hi rndhi borrow);
      hi <- (hi `>>` (W8.of_int 63));
      r <- (r + hi);
      i <- (i + (W64.of_int 1));
    }
    while ((i \ult (W64.of_int 166))) {
      hi <- (W64.of_int 524287);
      lo <- (BArray1328.get64 lop (W64.to_uint i));
      (borrow, lo) <- (sbb_64 lo rand_lo false);
      ( _1, hi) <- (sbb_64 hi rndhi borrow);
      hi <- (hi `>>` (W8.of_int 63));
      r <- (r + hi);
      i <- (i + (W64.of_int 1));
    }
    return r;
  }
  proc __smulh48 (a:W64.t, b:W64.t) : W64.t = {
    var r:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var tmp:W64.t;
    var rem:W64.t;
    rax <- a;
    (rdx, rax) <- (mulu_64 rax b);
    hi <- rdx;
    lo <- rax;
    tmp <- a;
    tmp <- (tmp `|>>` (W8.of_int 63));
    tmp <- (tmp `&` b);
    hi <- (hi - tmp);
    r <- hi;
    r <- (r `<<` (W8.of_int 16));
    tmp <- lo;
    tmp <- (tmp `>>` (W8.of_int 48));
    r <- (r `|` tmp);
    rem <- lo;
    rem <- (rem `&` (W64.of_int 281474976710655));
    tmp <- (W64.of_int 0);
    tmp <- (tmp - rem);
    rem <- (rem `|` tmp);
    rem <- (rem `>>` (W8.of_int 63));
    r <- (r + rem);
    return r;
  }
  proc _approx_exp (x:W64.t) : W64.t = {
    var result:W64.t;
    result <- (W64.of_int 55868746);
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 743564434));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 6953427278));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 55833338892));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 390932311155));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 2345623661771));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 11728123872951));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 46912496106200));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 140737488354861));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 281474976710650));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 281474976710657));
    return result;
  }
  proc __sample_gauss_sigma76_regs (randp:BArray26.t) : W64.t * W64.t *
                                                        W64.t * W64.t = {
    var rounded:W64.t;
    var sqr0:W64.t;
    var sqr1:W64.t;
    var accepted:W64.t;
    var byte:W8.t;
    var rand_gauss83_lo:W64.t;
    var t:W64.t;
    var u:W64.t;
    var rand_gauss83_hi:W32.t;
    var x:W64.t;
    var rand_rej:W64.t;
    var y0:W64.t;
    var y1:W64.t;
    var y:BArray16.t;
    var yp:BArray16.t;
    var sqrbuf:BArray16.t;
    var sqrp:BArray16.t;
    var exp_in:W64.t;
    var ms:W64.t;
    var exp:W64.t;
    sqrbuf <- witness;
    sqrp <- witness;
    y <- witness;
    yp <- witness;
    byte <- (BArray26.get8 randp 0);
    rand_gauss83_lo <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 1);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 2);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 3);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 4);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 5);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 6);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 48));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 7);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 56));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 8);
    u <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 9);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    u <- (u `|` t);
    byte <- (BArray26.get8 randp 10);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    u <- (u `|` t);
    u <- (u `&` (W64.of_int 524287));
    rand_gauss83_hi <- (truncateu32 u);
    x <@ _sample_gauss83 (rand_gauss83_lo, rand_gauss83_hi);
    byte <- (BArray26.get8 randp 11);
    rand_rej <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 12);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 13);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 14);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 15);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 16);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 17);
    y0 <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 18);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 19);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 20);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 21);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 22);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 23);
    y1 <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 24);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    y1 <- (y1 `|` t);
    byte <- (BArray26.get8 randp 25);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    y1 <- (y1 `|` t);
    t <- x;
    t <- (t `<<` (W8.of_int 24));
    y1 <- (y1 `|` t);
    rounded <- y0;
    rounded <- (rounded `>>` (W8.of_int 15));
    rounded <- (rounded + (W64.of_int 1));
    rounded <- (rounded `>>` (W8.of_int 1));
    t <- y1;
    t <- (t `<<` (W8.of_int 32));
    rounded <- (rounded + t);
    y <- (BArray16.set64 y 0 y0);
    y <- (BArray16.set64 y 1 y1);
    yp <- y;
    sqrp <- sqrbuf;
    sqrp <@ _fixpoint_square (sqrp, yp);
    sqr0 <- (BArray16.get64 sqrp 0);
    sqr1 <- (BArray16.get64 sqrp 1);
    exp_in <- sqr1;
    t <- x;
    t <- (t * x);
    t <- (t `<<` (W8.of_int 20));
    exp_in <- (exp_in - t);
    exp_in <- (exp_in `<<` (W8.of_int 20));
    t <- sqr0;
    t <- (t `>>` (W8.of_int 28));
    exp_in <- (exp_in `|` t);
    exp_in <- (exp_in + (W64.of_int 1));
    exp_in <- (exp_in `>>` (W8.of_int 1));
    (* Erased call to declassify *)
    ms <- (init_msf);
    exp_in <- (protect_64 exp_in ms);
    exp <@ _approx_exp (exp_in);
    accepted <- rand_rej;
    t <- rand_rej;
    t <- (t `&` (W64.of_int 1));
    accepted <- (accepted `^` t);
    accepted <- (accepted - exp);
    accepted <- (accepted `|>>` (W8.of_int 63));
    t <- (W64.of_int 0);
    t <- (t - rounded);
    u <- rounded;
    u <- (u `|` t);
    u <- (u `>>` (W8.of_int 63));
    u <- (u `|` rand_rej);
    accepted <- (accepted `&` u);
    accepted <- (accepted `&` (W64.of_int 1));
    return (rounded, sqr0, sqr1, accepted);
  }
  proc _sample_gauss_sigma76 (rp:BArray8.t, sqrp:BArray16.t,
                              acceptedp:BArray4.t, randp:BArray26.t) : 
  BArray8.t * BArray16.t * BArray4.t = {
    var sample:W64.t;
    var sqr0:W64.t;
    var sqr1:W64.t;
    var accepted:W64.t;
    (sample, sqr0, sqr1, accepted) <@ __sample_gauss_sigma76_regs (randp);
    rp <- (BArray8.set64 rp 0 sample);
    sqrp <- (BArray16.set64 sqrp 0 sqr0);
    sqrp <- (BArray16.set64 sqrp 1 sqr1);
    acceptedp <- (BArray4.set32 acceptedp 0 (truncateu32 accepted));
    return (rp, sqrp, acceptedp);
  }
  proc _sample_gauss (rp:BArray4096.t, sqsump:BArray16.t, coefcntp:BArray8.t,
                      bufp:BArray8192.t, counts:W64.t, dont_write_last:W64.t) : 
  BArray4096.t * BArray16.t * BArray8.t = {
    var srp:BArray4096.t;
    var ssqsump:BArray16.t;
    var scoefcntp:BArray8.t;
    var sbufp:BArray8192.t;
    var sdont:W64.t;
    var len:W64.t;
    var bytecnt:W64.t;
    var slen:W64.t;
    var sbytecnt:W64.t;
    var spos:W64.t;
    var scoefcnt:W64.t;
    var randbuf:BArray26.t;
    var randp:BArray26.t;
    var pos:W64.t;
    var bufp_tmp:BArray8192.t;
    var k:int;
    var byte:W8.t;
    var sample:W64.t;
    var sqr0:W64.t;
    var sqr1:W64.t;
    var accepted:W64.t;
    var coefcnt:W64.t;
    var ms:W64.t;
    var last_0:W64.t;
    var dont:W64.t;
    var rp_tmp:BArray4096.t;
    var accepted64:W64.t;
    var mask:W64.t;
    var sqsum_tmp:BArray16.t;
    var s0:W64.t;
    var s1:W64.t;
    var carry:W64.t;
    var coefcntp_tmp:BArray8.t;
    bufp_tmp <- witness;
    coefcntp_tmp <- witness;
    randbuf <- witness;
    randp <- witness;
    rp_tmp <- witness;
    sbufp <- witness;
    scoefcntp <- witness;
    sqsum_tmp <- witness;
    srp <- witness;
    ssqsump <- witness;
    srp <- rp;
    ssqsump <- sqsump;
    scoefcntp <- coefcntp;
    sbufp <- bufp;
    sdont <- dont_write_last;
    len <- counts;
    len <- (len `&` (W64.of_int 4294967295));
    bytecnt <- counts;
    bytecnt <- (bytecnt `>>` (W8.of_int 32));
    slen <- len;
    sbytecnt <- bytecnt;
    spos <- (W64.of_int 0);
    scoefcnt <- (W64.of_int 0);
    randp <- randbuf;
    coefcnt <- scoefcnt;
    len <- slen;
    while ((coefcnt \ult len)) {
      bytecnt <- sbytecnt;
      if ((bytecnt \ult (W64.of_int 26))) {
        slen <- coefcnt;
      } else {
        pos <- spos;
        bufp_tmp <- sbufp;
        k <- 0;
        while ((k < 26)) {
          byte <-
          (BArray8192.get8 bufp_tmp (W64.to_uint (pos + (W64.of_int k))));
          randp <- (BArray26.set8 randp k byte);
          k <- (k + 1);
        }
        (sample, sqr0, sqr1, accepted) <@ __sample_gauss_sigma76_regs (
        randp);
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        coefcnt <- (protect_64 coefcnt ms);
        len <- (protect_64 len ms);
        pos <- (protect_64 pos ms);
        bytecnt <- (protect_64 bytecnt ms);
        accepted <- (protect_64 accepted ms);
        last_0 <- len;
        last_0 <- (last_0 - (W64.of_int 1));
        dont <- sdont;
        (* Erased call to declassify *)
        dont <- (protect_64 dont ms);
        rp_tmp <- srp;
        rp_tmp <- (protect_ptr rp_tmp ms);
        if ((dont <> (W64.of_int 0))) {
          if ((coefcnt = last_0)) {
            accepted64 <- accepted;
          } else {
            rp_tmp <- (BArray4096.set64 rp_tmp (W64.to_uint coefcnt) sample);
            srp <- rp_tmp;
            accepted64 <- accepted;
          }
        } else {
          rp_tmp <- (BArray4096.set64 rp_tmp (W64.to_uint coefcnt) sample);
          srp <- rp_tmp;
          accepted64 <- accepted;
        }
        coefcnt <- (coefcnt + accepted64);
        pos <- (pos + (W64.of_int 26));
        bytecnt <- (bytecnt - (W64.of_int 26));
        mask <- (W64.of_int 0);
        mask <- (mask - accepted64);
        sqr0 <- (sqr0 `&` mask);
        sqr1 <- (sqr1 `&` mask);
        sqsum_tmp <- ssqsump;
        ms <- (init_msf);
        sqsum_tmp <- (protect_ptr sqsum_tmp ms);
        s0 <- (BArray16.get64 sqsum_tmp 0);
        s1 <- (BArray16.get64 sqsum_tmp 1);
        s0 <- (s0 + sqr0);
        s1 <- (s1 + sqr1);
        sqsum_tmp <- (BArray16.set64 sqsum_tmp 0 s0);
        sqsum_tmp <- (BArray16.set64 sqsum_tmp 1 s1);
        ssqsump <- sqsum_tmp;
        scoefcnt <- coefcnt;
        spos <- pos;
        sbytecnt <- bytecnt;
      }
      coefcnt <- scoefcnt;
      len <- slen;
    }
    sqsum_tmp <- ssqsump;
    s0 <- (BArray16.get64 sqsum_tmp 0);
    s1 <- (BArray16.get64 sqsum_tmp 1);
    carry <- s0;
    carry <- (carry `>>` (W8.of_int 48));
    s1 <- (s1 + carry);
    mask <- (W64.of_int 281474976710655);
    s0 <- (s0 `&` mask);
    sqsum_tmp <- (BArray16.set64 sqsum_tmp 0 s0);
    sqsum_tmp <- (BArray16.set64 sqsum_tmp 1 s1);
    ssqsump <- sqsum_tmp;
    coefcnt <- scoefcnt;
    coefcntp_tmp <- scoefcntp;
    coefcntp_tmp <- (BArray8.set64 coefcntp_tmp 0 coefcnt);
    scoefcntp <- coefcntp_tmp;
    rp <- srp;
    sqsump <- ssqsump;
    coefcntp <- scoefcntp;
    return (rp, sqsump, coefcntp);
  }
  proc sample_gauss83_jazz (rand_lo:W64.t, rand_hi:W32.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    ms <- (init_msf);
    rand_lo <- (protect_64 rand_lo ms);
    rand_hi <- (protect_32 rand_hi ms);
    r <@ _sample_gauss83 (rand_lo, rand_hi);
    return r;
  }
  proc smulh48_jazz (a:W64.t, b:W64.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    ms <- (init_msf);
    a <- (protect_64 a ms);
    b <- (protect_64 b ms);
    r <@ __smulh48 (a, b);
    return r;
  }
  proc approx_exp_jazz (x:W64.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    x <- (protect_64 x ms);
    r <@ _approx_exp (x);
    return r;
  }
  proc sample_gauss_sigma76_jazz (rp:BArray8.t, sqrp:BArray16.t,
                                  acceptedp:BArray4.t, randp:BArray26.t) : 
  BArray8.t * BArray16.t * BArray4.t = {
    var ms:W64.t;
    ms <- (init_msf);
    rp <- (protect_ptr rp ms);
    sqrp <- (protect_ptr sqrp ms);
    acceptedp <- (protect_ptr acceptedp ms);
    randp <- (protect_ptr randp ms);
    (rp, sqrp, acceptedp) <@ _sample_gauss_sigma76 (rp, sqrp, acceptedp,
    randp);
    return (rp, sqrp, acceptedp);
  }
  proc sample_gauss_jazz (rp:BArray4096.t, sqsump:BArray16.t,
                          coefcntp:BArray8.t, bufp:BArray8192.t,
                          counts:W64.t, dont_write_last:W64.t) : BArray4096.t *
                                                                 BArray16.t *
                                                                 BArray8.t = {
    var ms:W64.t;
    ms <- (init_msf);
    rp <- (protect_ptr rp ms);
    sqsump <- (protect_ptr sqsump ms);
    coefcntp <- (protect_ptr coefcntp ms);
    bufp <- (protect_ptr bufp ms);
    counts <- (protect_64 counts ms);
    dont_write_last <- (protect_64 dont_write_last ms);
    (rp, sqsump, coefcntp) <@ _sample_gauss (rp, sqsump, coefcntp, bufp,
    counts, dont_write_last);
    return (rp, sqsump, coefcntp);
  }
}.
