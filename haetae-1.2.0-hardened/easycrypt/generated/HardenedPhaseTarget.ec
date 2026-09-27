require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array2 Array4 Array24 Array76 Array166 Array256 Array512 Array2048 Array4096
WArray192 WArray304 WArray1024 WArray1328 BArray16 BArray32 BArray192
BArray304 BArray512 BArray1024 BArray1328 BArray8192 BArray32768.

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
  proc __bit_at_u8 (x:W32.t, shift:W8.t) : W8.t = {
    var r:W8.t;
    if ((shift = (W8.of_int 1))) {
      x <- (x `>>` (W8.of_int 1));
    } else {
      
    }
    if ((shift = (W8.of_int 2))) {
      x <- (x `>>` (W8.of_int 2));
    } else {
      
    }
    if ((shift = (W8.of_int 3))) {
      x <- (x `>>` (W8.of_int 3));
    } else {
      
    }
    if ((shift = (W8.of_int 4))) {
      x <- (x `>>` (W8.of_int 4));
    } else {
      
    }
    if ((shift = (W8.of_int 5))) {
      x <- (x `>>` (W8.of_int 5));
    } else {
      
    }
    if ((shift = (W8.of_int 6))) {
      x <- (x `>>` (W8.of_int 6));
    } else {
      
    }
    if ((shift = (W8.of_int 7))) {
      x <- (x `>>` (W8.of_int 7));
    } else {
      
    }
    x <- (x `&` (W32.of_int 1));
    r <- (truncateu8 x);
    return r;
  }
  proc __fixpoint_mul_regs (x0:W64.t, x1:W64.t, y0:W64.t, y1:W64.t) : 
  W64.t * W64.t = {
    var r0:W64.t;
    var r1:W64.t;
    var mask:W64.t;
    var lo:W64.t;
    var hi:W64.t;
    var tmp:W64.t;
    mask <- (W64.of_int 281474976710655);
    (lo, hi) <@ __mul48 (x0, y0);
    tmp <- lo;
    tmp <- (tmp `>>` (W8.of_int 47));
    tmp <- (tmp + (W64.of_int 1));
    tmp <- (tmp `>>` (W8.of_int 1));
    r0 <- hi;
    r0 <- (r0 + tmp);
    (lo, hi) <@ __mul48 (x0, y1);
    r0 <- (r0 + lo);
    r1 <- hi;
    (lo, hi) <@ __mul48 (x1, y0);
    r0 <- (r0 + lo);
    r1 <- (r1 + hi);
    tmp <- (W64.of_int 1);
    tmp <- (tmp `<<` (W8.of_int 27));
    r0 <- (r0 + tmp);
    r0 <- (r0 `>>` (W8.of_int 28));
    tmp <- r1;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    r1 <- (r1 `>>` (W8.of_int 28));
    tmp <- x1;
    (hi, tmp) <- (mulu_64 tmp y1);
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
  proc _hb_checked_mul_rnd13_regs (x:W64.t, y0:W64.t, y1:W64.t, sign:W64.t) : 
  W32.t * W64.t = {
    var ret:W32.t;
    var bad:W64.t;
    var x1:W64.t;
    var x0:W64.t;
    var r0:W64.t;
    var r1:W64.t;
    var magnitude:W64.t;
    var roundbit:W64.t;
    var mask:W64.t;
    x1 <- x;
    x1 <- (x1 `>>` (W8.of_int 32));
    x0 <- x;
    x0 <- (x0 `&` (W64.of_int 4294967295));
    x0 <- (x0 `<<` (W8.of_int 16));
    (r0, r1) <@ __fixpoint_mul_regs (x0, x1, y0, y1);
    magnitude <- r1;
    magnitude <- (magnitude `>>` (W8.of_int 15));
    roundbit <- r1;
    roundbit <- (roundbit `>>` (W8.of_int 14));
    roundbit <- (roundbit `&` (W64.of_int 1));
    magnitude <- (magnitude + roundbit);
    bad <- (W64.of_int 2147483647);
    bad <- (bad - magnitude);
    bad <- (bad `|>>` (W8.of_int 63));
    mask <- (W64.of_int 0);
    mask <- (mask - sign);
    magnitude <- (magnitude `^` mask);
    magnitude <- (magnitude + sign);
    ret <- (truncateu32 magnitude);
    return (ret, bad);
  }
  proc _hb_checked_mul_rnd13 (x:W64.t, yp:BArray16.t, sign:W8.t) : W32.t *
                                                                   W64.t = {
    var ret:W32.t;
    var bad:W64.t;
    var ms:W64.t;
    var y0:W64.t;
    var y1:W64.t;
    var s:W64.t;
    ms <- (init_msf);
    yp <- (protect_ptr yp ms);
    y0 <- (BArray16.get64 yp 0);
    y1 <- (BArray16.get64 yp 1);
    s <- (zeroextu64 sign);
    (ret, bad) <@ _hb_checked_mul_rnd13_regs (x, y0, y1, s);
    return (ret, bad);
  }
  proc _hb_checked_scale_samples (y1p:BArray8192.t, y2p:BArray8192.t,
                                  samplesp:BArray32768.t, signsp:BArray512.t,
                                  scalep:BArray16.t, counts:W64.t) : 
  BArray8192.t * BArray8192.t * W64.t = {
    var bad:W64.t;
    var lcount:W64.t;
    var total:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var byte_idx:W64.t;
    var sign32:W32.t;
    var shift:W8.t;
    var sign8:W8.t;
    var sample:W64.t;
    var r:W32.t;
    var item_bad:W64.t;
    var j:W64.t;
    lcount <- counts;
    lcount <- (lcount `&` (W64.of_int 4294967295));
    total <- counts;
    total <- (total `>>` (W8.of_int 32));
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    samplesp <- (protect_ptr samplesp ms);
    signsp <- (protect_ptr signsp ms);
    scalep <- (protect_ptr scalep ms);
    lcount <- (protect_64 lcount ms);
    total <- (protect_64 total ms);
    bad <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult lcount)) {
      byte_idx <- i;
      byte_idx <- (byte_idx `>>` (W8.of_int 3));
      sign32 <- (zeroextu32 (BArray512.get8 signsp (W64.to_uint byte_idx)));
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      sign8 <@ __bit_at_u8 (sign32, shift);
      sample <- (BArray32768.get64 samplesp (W64.to_uint i));
      (* Erased call to spill *)
      (r, item_bad) <@ _hb_checked_mul_rnd13 (sample, scalep, sign8);
      (* Erased call to unspill *)
      bad <- (bad `|` item_bad);
      ms <- (init_msf);
      y1p <- (protect_ptr y1p ms);
      y2p <- (protect_ptr y2p ms);
      samplesp <- (protect_ptr samplesp ms);
      signsp <- (protect_ptr signsp ms);
      scalep <- (protect_ptr scalep ms);
      lcount <- (protect_64 lcount ms);
      total <- (protect_64 total ms);
      i <- (protect_64 i ms);
      y1p <- (BArray8192.set32 y1p (W64.to_uint i) r);
      i <- (i + (W64.of_int 1));
    }
    j <- (W64.of_int 0);
    while ((i \ult total)) {
      byte_idx <- i;
      byte_idx <- (byte_idx `>>` (W8.of_int 3));
      sign32 <- (zeroextu32 (BArray512.get8 signsp (W64.to_uint byte_idx)));
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      sign8 <@ __bit_at_u8 (sign32, shift);
      sample <- (BArray32768.get64 samplesp (W64.to_uint i));
      (* Erased call to spill *)
      (r, item_bad) <@ _hb_checked_mul_rnd13 (sample, scalep, sign8);
      (* Erased call to unspill *)
      bad <- (bad `|` item_bad);
      ms <- (init_msf);
      y1p <- (protect_ptr y1p ms);
      y2p <- (protect_ptr y2p ms);
      samplesp <- (protect_ptr samplesp ms);
      signsp <- (protect_ptr signsp ms);
      scalep <- (protect_ptr scalep ms);
      total <- (protect_64 total ms);
      i <- (protect_64 i ms);
      j <- (protect_64 j ms);
      y2p <- (BArray8192.set32 y2p (W64.to_uint j) r);
      i <- (i + (W64.of_int 1));
      j <- (j + (W64.of_int 1));
    }
    return (y1p, y2p, bad);
  }
  proc _hb_checked_sqnorm2_2048 (ap:BArray8192.t, acount:W64.t,
                                 bp:BArray8192.t, bcount:W64.t) : W64.t *
                                                                  W64.t = {
    var total:W64.t;
    var overflow:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var a:W32.t;
    var coeff:W64.t;
    var prod:W64.t;
    var carry:bool;
    var  _0:bool;
    var  _1:bool;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    ap <- (protect_ptr ap ms);
    bp <- (protect_ptr bp ms);
    acount <- (protect_64 acount ms);
    bcount <- (protect_64 bcount ms);
    total <- (W64.of_int 0);
    overflow <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult acount)) {
      a <- (BArray8192.get32 ap (W64.to_uint i));
      coeff <- (sigextu64 a);
      prod <- (coeff * coeff);
      (carry, total) <- (adc_64 total prod false);
      ( _0, prod) <- (sbb_64 prod prod carry);
      overflow <- (overflow `|` prod);
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult bcount)) {
      a <- (BArray8192.get32 bp (W64.to_uint i));
      coeff <- (sigextu64 a);
      prod <- (coeff * coeff);
      (carry, total) <- (adc_64 total prod false);
      ( _1, prod) <- (sbb_64 prod prod carry);
      overflow <- (overflow `|` prod);
      i <- (i + (W64.of_int 1));
    }
    return (total, overflow);
  }
  proc _hb_checked_scale_and_check_values (y1p:BArray8192.t,
                                           y2p:BArray8192.t,
                                           samplesp:BArray32768.t,
                                           signsp:BArray512.t,
                                           scalep:BArray16.t, lcount:W64.t,
                                           total:W64.t, bound:W64.t) : 
  BArray8192.t * BArray8192.t * W64.t = {
    var accepted:W64.t;
    var ms:W64.t;
    var slcount:W64.t;
    var stotal:W64.t;
    var sbound:W64.t;
    var counts:W64.t;
    var bad:W64.t;
    var sy1p:BArray8192.t;
    var sy2p:BArray8192.t;
    var sbad:W64.t;
    var kcount:W64.t;
    var norm:W64.t;
    var overflow:W64.t;
    var compare:W64.t;
    var borrow:bool;
    var  _0:bool;
    sy1p <- witness;
    sy2p <- witness;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    samplesp <- (protect_ptr samplesp ms);
    signsp <- (protect_ptr signsp ms);
    scalep <- (protect_ptr scalep ms);
    lcount <- (protect_64 lcount ms);
    total <- (protect_64 total ms);
    bound <- (protect_64 bound ms);
    slcount <- lcount;
    stotal <- total;
    sbound <- bound;
    counts <- total;
    counts <- (counts `<<` (W8.of_int 32));
    counts <- (counts `|` lcount);
    (y1p, y2p, bad) <@ _hb_checked_scale_samples (y1p, y2p, samplesp, 
    signsp, scalep, counts);
    sy1p <- y1p;
    sy2p <- y2p;
    sbad <- bad;
    lcount <- slcount;
    kcount <- stotal;
    kcount <- (kcount - lcount);
    (norm, overflow) <@ _hb_checked_sqnorm2_2048 (y1p, lcount, y2p, kcount);
    bad <- sbad;
    bad <- (bad `|` overflow);
    compare <- sbound;
    (borrow, compare) <- (sbb_64 compare norm false);
    ( _0, compare) <- (sbb_64 compare compare borrow);
    bad <- (bad `|` compare);
    bad <- (bad `^` (W64.of_int 18446744073709551615));
    accepted <- bad;
    accepted <- (accepted `&` (W64.of_int 1));
    (* Erased call to declassify *)
    ms <- (init_msf);
    accepted <- (protect_64 accepted ms);
    y1p <- sy1p;
    y2p <- sy2p;
    return (y1p, y2p, accepted);
  }
  proc _polyfixveclk_scale_and_check (y1p:BArray8192.t, y2p:BArray8192.t,
                                      statep:BArray32.t,
                                      samplesp:BArray32768.t,
                                      signsp:BArray512.t, scalep:BArray16.t) : 
  BArray8192.t * BArray8192.t * BArray32.t = {
    var ms:W64.t;
    var sstatep:BArray32.t;
    var lcount:W64.t;
    var total:W64.t;
    var bound:W64.t;
    var accepted:W64.t;
    sstatep <- witness;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    sstatep <- statep;
    lcount <- (BArray32.get64 statep 0);
    total <- (BArray32.get64 statep 1);
    bound <- (BArray32.get64 statep 2);
    (y1p, y2p, accepted) <@ _hb_checked_scale_and_check_values (y1p, 
    y2p, samplesp, signsp, scalep, lcount, total, bound);
    statep <- sstatep;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray32.set64 statep 3 accepted);
    return (y1p, y2p, statep);
  }
  proc polyfixveclk_scale_and_check_jazz (y1p:BArray8192.t, y2p:BArray8192.t,
                                          statep:BArray32.t,
                                          samplesp:BArray32768.t,
                                          signsp:BArray512.t,
                                          scalep:BArray16.t) : BArray8192.t *
                                                               BArray8192.t *
                                                               BArray32.t = {
    var ms:W64.t;
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    statep <- (protect_ptr statep ms);
    samplesp <- (protect_ptr samplesp ms);
    signsp <- (protect_ptr signsp ms);
    scalep <- (protect_ptr scalep ms);
    (y1p, y2p, statep) <@ _polyfixveclk_scale_and_check (y1p, y2p, statep,
    samplesp, signsp, scalep);
    return (y1p, y2p, statep);
  }
}.
