module AllProblems where
import Prelude hiding (all,and,not,or)
import Boolean
import Montague
problem 1 = do
  violinist <- newPred
  musician <- newPred
  readMusic <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP every violinist) (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP genericPl musician) (modify generally readMusic))
  return $ if_ (cltoS pos (s1 john (bare (isA violinist)))) (cltoS pos (s1 john (bare readMusic)))
problem 2 = do
  interLogicStudent <- newPred
  prologProgrammer <- newPred
  readMusic <- newPred
  observe $ cltoS pos (s1 (qNP genericPl prologProgrammer) (modify always (isA interLogicStudent)))
  observe $ cltoS pos (s1 (qNP genericPl interLogicStudent) (modify rarely readMusic))
  return $ cltoS neg (s1 (qNP genericPl prologProgrammer) (bare readMusic))
problem 3 = do
  baldMan <- newPred
  toupeeWearer <- newPred
  tryHairTransplantTreatment <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP many baldMan) (bare (isA toupeeWearer)))
  observe $ cltoS pos (s1 (qNP genericPl toupeeWearer) (modify always tryHairTransplantTreatment))
  observe $ cltoS pos (s1 john (bare (isA baldMan)))
  return $ cltoS pos (s1 john (bare tryHairTransplantTreatment))
problem 4 = do
  basketballPlayer <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (isA basketballPlayer)))
  observe $ cltoS pos (s1 (qNP genericPl basketballPlayer) (modify usually (moreVP tall (qNP genericPl (non basketballPlayer)))))
  return $ cltoS pos (s1 john (bare (moreVP tall (qNP most person))))
problem 5 = do
  basketballPlayer <- newPred
  john <- PN <$> newInd
  short <- newMeasure
  observe $ cltoS pos (s1 john (bare (isA (qual short basketballPlayer))))
  observe $ cltoS pos (s1 (qNP genericPl basketballPlayer) (modify usually (comparVP less short (qNP genericPl (non basketballPlayer)))))
  return $ cltoS pos (s1 john (bare (testVP short)))
problem 6 = do
  basketballPlayer <- newPred
  tall <- newMeasure
  observe $ cltoS pos (s1 (qNP all basketballPlayer) (modify probably (testVP tall)))
  return $ cltoS pos (s1 (qNP most basketballPlayer) (bare (testVP tall)))
problem 7 = do
  violinist <- newPred
  prologProgrammer <- newPred
  readMusic <- newPred
  observe $ cltoS pos (s1 (percentOf (digitsToCard (addDigit n4_Dig (oneDigit n0_Dig))) prologProgrammer) (bare readMusic))
  observe $ cltoS neg (s1 (qNP genericPl violinist) (bare (like (qNP genericPl (relativiseCN prologProgrammer (makepolarRS pos (makeRCL tHAT readMusic)))))))
  return $ cltoS neg (s1 (qNP genericPl violinist) (bare (like (qNP most prologProgrammer))))
problem 8 = do
  prologProgrammer <- newPred
  logician <- newPred
  useTailRec <- newPred
  observe $ cltoS pos (s1 (qNP genericPl prologProgrammer) (modify definitely useTailRec))
  observe $ cltoS pos (s1 (qNP many logician) (bare (isA prologProgrammer)))
  return $ cltoS pos (s1 (qNP genericPl logician) (bare useTailRec))
problem 9 = do
  stonesFan <- newPred
  preferTheDoorsToTheBeatles <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP genericPl stonesFan) (modify often preferTheDoorsToTheBeatles))
  observe $ cltoS pos (s1 john (bare (isA stonesFan)))
  return $ cltoS pos (s1 john (bare preferTheDoorsToTheBeatles))
problem 10 = do
  playInMF <- newPred
  playForTheLeafs <- newPred
  john <- PN <$> newInd
  tradedFromTheCanadiens <- newMeasure
  observe $ if_ (cltoS pos (s1 genericYou (bare playForTheLeafs))) (cltoS pos (s1 genericYou (modify probably (testVP tradedFromTheCanadiens))))
  observe $ if_ (cltoS pos (s1 genericYou (bare (testVP tradedFromTheCanadiens)))) (cltoS pos (s1 genericYou (modify often playInMF)))
  observe $ cltoS pos (s1 john (bare playForTheLeafs))
  return $ cltoS pos (s1 john (bare playInMF))
problem 11 = do
  turkishCoffeeDrinker <- newPred
  listenToOudMusic <- newPred
  enjoyArak <- newPred
  observe $ cltoS pos (s1 (qNP genericPl turkishCoffeeDrinker) (modify frequently enjoyArak))
  observe $ cltoS pos (s1 (qNP most (relativiseCN person (makepolarRS pos (makeRCL tHAT enjoyArak)))) (modify also listenToOudMusic))
  return $ cltoS pos (s1 (qNP genericPl turkishCoffeeDrinker) (bare listenToOudMusic))
problem 12 = do
  eatHumus <- newPred
  enjoyTabouli <- newPred
  insistOnMintTeaWithFood <- newPred
  observe $ if_ (cltoS pos (s1 genericYou (modify regularly eatHumus))) (cltoS pos (s1 genericYou (modify also enjoyTabouli)))
  observe $ cltoS pos (s1 (qNP most (relativiseCN person (makepolarRS pos (makeRCL tHAT enjoyTabouli)))) (bare insistOnMintTeaWithFood))
  return $ if_ (cltoS pos (s1 genericYou (bare eatHumus))) (cltoS pos (s1 genericYou (bare insistOnMintTeaWithFood)))
problem 13 = do
  cricketPlayer <- newPred
  hitRun <- newPred
  mary <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP genericPl cricketPlayer) (modify rarely hitRun))
  observe $ cltoS pos (s1 mary (bare hitRun))
  return $ cltoS neg (s1 mary (bare (isA cricketPlayer)))
problem 14 = do
  violinist <- newPred
  jazzGuitarist <- newPred
  john <- PN <$> newInd
  canPlayChoords <- mkCanPlayChoords
  observe $ cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (addDigit n0_Dig (oneDigit n0_Dig)))))))
  observe $ cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (oneDigit n0_Dig))))))
  observe $ cltoS pos (s1 john (bare (canPlayChoords more (digitsToCard (addDigit n8_Dig (oneDigit n0_Dig))))))
  return $ cltoS pos (s1 john (bare (isA jazzGuitarist)))
problem 15 = do
  mary <- PN <$> newInd
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 john (bare (moreVP tall mary)))
  return $ cltoS pos (s1 john (bare (testVP tall)))
problem 16 = do
  mary <- PN <$> newInd
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS neg (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 mary (bare (moreVP tall john)))
  return $ cltoS neg (s1 john (bare (testVP tall)))
problem 17 = do
  mary <- PN <$> newInd
  john <- PN <$> newInd
  sam <- PN <$> newInd
  punctual <- newMeasure
  observe $ cltoS pos (s1 john (modify always (comparVP equal punctual mary)))
  observe $ cltoS pos (s1 sam (modify usually (comparVP more punctual john)))
  return $ cltoS pos (s1 sam (bare (comparVP more punctual mary)))
problem 18 = do
  linguist <- newPred
  knowFLT <- newPred
  dislikeExperimentalWork <- newPred
  observe $ cltoS pos (s1 (qNP many linguist) (bare knowFLT))
  observe $ cltoS pos (s1 (qNP most (relativiseCN linguist (makepolarRS pos (makeRCL tHAT knowFLT)))) (bare dislikeExperimentalWork))
  return $ cltoS pos (s1 (qNP many linguist) (bare dislikeExperimentalWork))
problem 19 = do
  conservative <- newPred
  supportFreeUniversityEducation <- newPred
  john <- PN <$> newInd
  observe $ cltoS neg (s1 (qNP most conservative) (modify usually supportFreeUniversityEducation))
  observe $ cltoS pos (s1 john (bare supportFreeUniversityEducation))
  return $ cltoS neg (s1 john (bare (isA conservative)))
problem 20 = do
  stonesFan <- newPred
  guitarist <- newPred
  preferTheDoorsToTheBeatles <- newPred
  observe $ if_ (cltoS pos (s1 genericYou (bare (isA guitarist)))) (cltoS pos (s1 genericYou (modify probably (isA stonesFan))))
  observe $ if_ (cltoS pos (s1 genericYou (bare (isA stonesFan)))) (cltoS pos (s1 genericYou (modify generally preferTheDoorsToTheBeatles)))
  return $ not (cltoS pos (s1 (qNP every (relativiseCN person (makepolarRS neg (makeRCL tHAT preferTheDoorsToTheBeatles)))) (bare (isA (relativiseCN person (makepolarRS neg (makeRCL tHAT (isA guitarist))))))))
problem 21 = do
  stonesFan <- newPred
  guitarist <- newPred
  preferTheDoorsToTheBeatles <- newPred
  observe $ if_ (cltoS pos (s1 genericYou (bare (isA guitarist)))) (cltoS pos (s1 genericYou (modify probably (isA stonesFan))))
  observe $ if_ (cltoS pos (s1 genericYou (bare (isA stonesFan)))) (cltoS pos (s1 genericYou (modify generally preferTheDoorsToTheBeatles)))
  return $ cltoS neg (s1 (qNP every (relativiseCN person (makepolarRS neg (makeRCL tHAT preferTheDoorsToTheBeatles)))) (bare (isA guitarist)))
problem 22 = do
  basketballPlayer <- newPred
  tall <- newMeasure
  observe $ cltoS pos (s1 (percentOf (digitsToCard (addDigit n8_Dig (oneDigit n0_Dig))) basketballPlayer) (bare (testVP tall)))
  return $ cltoS pos (s1 (qNP genericPl basketballPlayer) (modify probably (testVP tall)))
problem 23 = do
  basketballPlayer <- newPred
  tall <- newMeasure
  observe $ cltoS pos (s1 (percentOf (digitsToCard (addDigit n8_Dig (oneDigit n0_Dig))) basketballPlayer) (bare (testVP tall)))
  return $ cltoS neg (s1 (qNP few basketballPlayer) (bare (testVP tall)))
problem 24 = do
  prologProgrammer <- newPred
  logician <- newPred
  useTailRec <- newPred
  observe $ cltoS pos (s1 (qNP genericPl prologProgrammer) (modify definitely useTailRec))
  observe $ cltoS pos (s1 (qNP genericPl logician) (modify frequently (isA prologProgrammer)))
  return $ cltoS pos (s1 (qNP genericPl logician) (modify probably useTailRec))
problem 25 = do
  guitarist <- newPred
  logician <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (testVP tall)))
  observe $ cltoS pos (s1 (qNP all guitarist) (bare (isA logician)))
  return $ and (cltoS pos (s1 john (bare (testVP tall)))) (cltoS pos (s1 (qNP all guitarist) (bare (isA logician))))
problem 26 = do
  guitarist <- newPred
  logician <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (testVP tall)))
  observe $ cltoS pos (s1 (qNP all guitarist) (bare (isA logician)))
  return $ cltoS pos (s1 john (bare (testVP tall)))
problem 27 = do
  mary <- PN <$> newInd
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (moreVP tall mary)))
  return $ cltoS pos (s1 john (bare (testVP tall)))
problem 28 = do
  mary <- PN <$> newInd
  john <- PN <$> newInd
  sam <- PN <$> newInd
  molly <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (moreVP tall mary)))
  observe $ cltoS pos (s1 mary (bare (moreVP tall sam)))
  return $ cltoS pos (s1 john (bare (moreVP tall molly)))
problem 29 = do
  mary <- PN <$> newInd
  john <- PN <$> newInd
  sam <- PN <$> newInd
  kate <- PN <$> newInd
  christine <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (moreVP tall mary)))
  observe $ cltoS pos (s1 sam (bare (moreVP tall mary)))
  observe $ cltoS pos (s1 kate (bare (moreVP tall christine)))
  return $ cltoS pos (s1 kate (bare (moreVP tall john)))
problem 30 = do
  stonesFan <- newPred
  interLogicStudent <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP all interLogicStudent) (bare (isA stonesFan)))
  observe $ cltoS pos (s1 john (bare (isA interLogicStudent)))
  return $ cltoS pos (s1 john (bare (isA stonesFan)))
problem 31 = do
  guitarist <- newPred
  logician <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 john (bare (isA guitarist)))
  observe $ cltoS neg (s1 (qNP most guitarist) (bare (isA logician)))
  return $ cltoS neg (s1 john (bare (isA logician)))
problem 32 = do
  guitarist <- newPred
  logician <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 john (bare (isA logician)))
  observe $ cltoS neg (s1 (qNP most guitarist) (bare (isA logician)))
  return $ cltoS neg (s1 john (bare (isA guitarist)))
problem 33 = do
  john <- PN <$> newInd
  tall <- newMeasure
  return $ not (cltoS pos (s1 john (bare (moreVP tall (qNP most person)))))
problem 34 = do
  john <- PN <$> newInd
  short <- newMeasure
  return $ cltoS pos (s1 (qNP aFew person) (bare (moreVP short john)))
problem 35 = do
  john <- PN <$> newInd
  short <- newMeasure
  return $ not (cltoS pos (s1 (qNP few person) (bare (moreVP short john))))
problem 36 = do
  guitarist <- newPred
  john <- PN <$> newInd
  observe $ cltoS neg (s1 john (bare (isA guitarist)))
  return $ not (cltoS pos (s1 john (bare (isA guitarist))))
problem 37 = do
  mary <- PN <$> newInd
  molly <- PN <$> newInd
  kate <- PN <$> newInd
  athena <- PN <$> newInd
  helen <- PN <$> newInd
  artemis <- PN <$> newInd
  joanna <- PN <$> newInd
  christine <- PN <$> newInd
  ruth <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 molly (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n4_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 molly (bare (testVP tall)))
  observe $ cltoS pos (s1 ruth (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 ruth (bare (testVP tall)))
  observe $ cltoS pos (s1 helen (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n7_Dig (oneDigit n8_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 helen (bare (testVP tall)))
  observe $ cltoS pos (s1 athena (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n6_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 athena (bare (testVP tall)))
  observe $ cltoS pos (s1 artemis (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n5_Dig (oneDigit n7_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 artemis (bare (testVP tall)))
  observe $ cltoS pos (s1 joanna (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 joanna (bare (testVP tall)))
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n2_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n7_Dig (oneDigit n8_Dig)))) centimeter tall)))
  return $ cltoS pos (s1 christine (bare (testVP tall)))
problem 38 = do
  mary <- PN <$> newInd
  molly <- PN <$> newInd
  kate <- PN <$> newInd
  athena <- PN <$> newInd
  helen <- PN <$> newInd
  artemis <- PN <$> newInd
  joanna <- PN <$> newInd
  christine <- PN <$> newInd
  ruth <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n9_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 molly (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n4_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 molly (bare (testVP tall)))
  observe $ cltoS pos (s1 ruth (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 ruth (bare (testVP tall)))
  observe $ cltoS pos (s1 helen (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n7_Dig (oneDigit n8_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 helen (bare (testVP tall)))
  observe $ cltoS pos (s1 athena (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n6_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 athena (bare (testVP tall)))
  observe $ cltoS pos (s1 artemis (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n5_Dig (oneDigit n7_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 artemis (bare (testVP tall)))
  observe $ cltoS pos (s1 joanna (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 joanna (bare (testVP tall)))
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n2_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n3_Dig)))) centimeter tall)))
  return $ cltoS neg (s1 christine (bare (testVP tall)))
problem 39 = do
  violinist <- newPred
  jazzGuitarist <- newPred
  john <- PN <$> newInd
  canPlayChoords <- mkCanPlayChoords
  observe $ cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords more (digitsToCard (oneDigit n2_Dig)))))
  observe $ cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords more (digitsToCard (oneDigit n1_Dig)))))
  observe $ cltoS pos (s1 john (bare (canPlayChoords more (digitsToCard (oneDigit n2_Dig)))))
  return $ cltoS pos (s1 john (bare (isA jazzGuitarist)))
problem 40 = do
  violinist <- newPred
  jazzGuitarist <- newPred
  john <- PN <$> newInd
  canPlayChoords <- mkCanPlayChoords
  observe $ cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords more (digitsToCard (oneDigit n5_Dig)))))
  observe $ cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords more (digitsToCard (oneDigit n2_Dig)))))
  observe $ cltoS pos (s1 john (bare (canPlayChoords more (digitsToCard (oneDigit n4_Dig)))))
  return $ cltoS pos (s1 john (bare (isA jazzGuitarist)))
problem 41 = do
  mary <- PN <$> newInd
  john <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  foot <- newUnit
  observe $ cltoS pos (s1 john (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 john (bare (measure (digitsToCard (oneDigit n6_Dig)) foot tall)))
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (oneDigit n6_Dig)) foot tall)))
  return $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n0_Dig)))) centimeter tall)))
problem 42 = do
  mary <- PN <$> newInd
  molly <- PN <$> newInd
  kate <- PN <$> newInd
  athena <- PN <$> newInd
  helen <- PN <$> newInd
  artemis <- PN <$> newInd
  joanna <- PN <$> newInd
  christine <- PN <$> newInd
  ruth <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 molly (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n4_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 molly (bare (testVP tall)))
  observe $ cltoS pos (s1 ruth (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 ruth (bare (testVP tall)))
  observe $ cltoS pos (s1 helen (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n7_Dig (oneDigit n8_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 helen (bare (testVP tall)))
  observe $ cltoS pos (s1 athena (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n6_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 athena (bare (testVP tall)))
  observe $ cltoS pos (s1 artemis (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n5_Dig (oneDigit n7_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 artemis (bare (testVP tall)))
  observe $ cltoS pos (s1 joanna (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 joanna (bare (testVP tall)))
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n2_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n7_Dig (oneDigit n1_Dig)))) centimeter tall)))
  return $ and (parens (not (cltoS pos (s1 christine (bare (testVP tall)))))) (parens (not (cltoS neg (s1 christine (bare (testVP tall))))))
problem 43 = return parseFailure
problem 44 = return parseFailure
problem 45 = return parseFailure
problem 46 = return parseFailure
problem 47 = do
  basketballPlayer <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (isA basketballPlayer)))
  observe $ cltoS pos (s1 (qNP genericPl basketballPlayer) (bare (testVP tall)))
  return $ cltoS pos (s1 john (bare (moreVP tall (percentOf (digitsToCard (addDigit n5_Dig (oneDigit n0_Dig))) person))))
problem 48 = do
  violinist <- newPred
  jazzGuitarist <- newPred
  john <- PN <$> newInd
  canPlayChoords <- mkCanPlayChoords
  observe $ cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (addDigit n0_Dig (oneDigit n0_Dig)))))))
  observe $ cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (oneDigit n0_Dig))))))
  observe $ cltoS pos (s1 john (bare (canPlayChoords more (digitsToCard (addDigit n8_Dig (oneDigit n0_Dig))))))
  return $ cltoS neg (s1 john (bare (isA violinist)))
problem 49 = do
  violinist <- newPred
  jazzGuitarist <- newPred
  john <- PN <$> newInd
  canPlayChoords <- mkCanPlayChoords
  observe $ cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (addDigit n0_Dig (oneDigit n0_Dig)))))))
  observe $ cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (oneDigit n0_Dig))))))
  observe $ cltoS pos (s1 john (bare (canPlayChoords less (digitsToCard (addDigit n1_Dig (oneDigit n5_Dig))))))
  return $ cltoS pos (s1 john (bare (isA violinist)))
problem 50 = do
  violinist <- newPred
  jazzGuitarist <- newPred
  john <- PN <$> newInd
  canPlayChoords <- mkCanPlayChoords
  observe $ cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (addDigit n0_Dig (oneDigit n0_Dig)))))))
  observe $ cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (oneDigit n0_Dig))))))
  observe $ cltoS pos (s1 john (bare (canPlayChoords more (digitsToCard (addDigit n9_Dig (oneDigit n0_Dig))))))
  return $ cltoS pos (s1 john (bare (isA jazzGuitarist)))
problem 51 = do
  violinist <- newPred
  musician <- newPred
  jazzGuitarist <- newPred
  john <- PN <$> newInd
  canPlayChoords <- mkCanPlayChoords
  observe $ cltoS pos (s1 (qNP genericPl jazzGuitarist) (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP genericPl violinist) (bare (isA musician)))
  observe $ cltoS pos (s1 john (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (addDigit n0_Dig (oneDigit n0_Dig)))))))
  observe $ cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (oneDigit n0_Dig))))))
  observe $ cltoS pos (s1 john (bare (canPlayChoords more (digitsToCard (addDigit n9_Dig (oneDigit n0_Dig))))))
  return $ cltoS pos (s1 john (bare (isA jazzGuitarist)))
problem 52 = do
  violinist <- newPred
  musician <- newPred
  jazzGuitarist <- newPred
  john <- PN <$> newInd
  canPlayChoords <- mkCanPlayChoords
  observe $ cltoS pos (s1 (qNP genericPl jazzGuitarist) (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP genericPl violinist) (bare (isA musician)))
  observe $ cltoS pos (s1 john (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP genericPl musician) (bare (canPlayChoords more (digitsToCard (oneDigit n1_Dig)))))
  observe $ cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (addDigit n0_Dig (oneDigit n0_Dig)))))))
  observe $ cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords more (digitsToCard (addDigit n1_Dig (oneDigit n0_Dig))))))
  observe $ cltoS pos (s1 john (bare (canPlayChoords more (digitsToCard (addDigit n9_Dig (oneDigit n0_Dig))))))
  return $ cltoS pos (s1 john (bare (isA jazzGuitarist)))
problem 53 = do
  basketballPlayer <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (isA basketballPlayer)))
  observe $ cltoS pos (s1 (qNP genericPl basketballPlayer) (bare (moreVP tall (qNP most (non basketballPlayer)))))
  return $ cltoS pos (s1 john (bare (moreVP tall (qNP most (non basketballPlayer)))))
problem 54 = do
  basketballPlayer <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 (qNP few person) (bare (isA basketballPlayer)))
  observe $ cltoS pos (s1 (qNP genericPl basketballPlayer) (bare (moreVP tall (qNP most (non basketballPlayer)))))
  observe $ cltoS pos (s1 john (bare (isA basketballPlayer)))
  return $ cltoS pos (s1 john (bare (moreVP tall (qNP most person))))
problem 55 = do
  basketballPlayer <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 (percentOf (digitsToCard (addDigit n9_Dig (oneDigit n9_Dig))) person) (bare (isA (non basketballPlayer))))
  observe $ cltoS pos (s1 (qNP genericPl basketballPlayer) (bare (moreVP tall (qNP most (non basketballPlayer)))))
  observe $ cltoS pos (s1 john (bare (isA basketballPlayer)))
  return $ cltoS pos (s1 john (bare (moreVP tall (qNP most person))))
problem 56 = do
  eatHumus <- newPred
  enjoyTabouli <- newPred
  insistOnMintTeaWithFood <- newPred
  observe $ if_ (cltoS pos (s1 genericYou (modify regularly eatHumus))) (cltoS pos (s1 genericYou (modify also enjoyTabouli)))
  observe $ cltoS pos (s1 (qNP genericPl (relativiseCN person (makepolarRS pos (makeRCL tHAT enjoyTabouli)))) (bare insistOnMintTeaWithFood))
  return $ if_ (cltoS pos (s1 genericYou (modify regularly eatHumus))) (cltoS pos (s1 genericYou (bare insistOnMintTeaWithFood)))
problem 57 = do
  eatHumus <- newPred
  enjoyTabouli <- newPred
  insistOnMintTeaWithFood <- newPred
  observe $ if_ (cltoS pos (s1 genericYou (bare eatHumus))) (cltoS pos (s1 genericYou (modify also enjoyTabouli)))
  observe $ cltoS pos (s1 (qNP genericPl (relativiseCN person (makepolarRS pos (makeRCL tHAT enjoyTabouli)))) (bare insistOnMintTeaWithFood))
  return $ if_ (cltoS pos (s1 genericYou (bare eatHumus))) (cltoS pos (s1 genericYou (bare insistOnMintTeaWithFood)))
problem 58 = do
  eatHumus <- newPred
  enjoyTabouli <- newPred
  john <- PN <$> newInd
  observe $ if_ (cltoS pos (s1 genericYou (bare eatHumus))) (cltoS pos (s1 genericYou (modify also enjoyTabouli)))
  observe $ cltoS pos (s1 john (bare eatHumus))
  return $ cltoS pos (s1 john (bare enjoyTabouli))
problem 59 = do
  eatHumus <- newPred
  enjoyTabouli <- newPred
  insistOnMintTeaWithFood <- newPred
  john <- PN <$> newInd
  observe $ if_ (cltoS pos (s1 genericYou (bare eatHumus))) (cltoS pos (s1 genericYou (modify also enjoyTabouli)))
  observe $ cltoS pos (s1 (qNP genericPl (relativiseCN person (makepolarRS pos (makeRCL tHAT enjoyTabouli)))) (bare insistOnMintTeaWithFood))
  return $ if_ (cltoS pos (s1 john (bare eatHumus))) (cltoS pos (s1 john (bare insistOnMintTeaWithFood)))
problem 60 = do
  eatHumus <- newPred
  enjoyTabouli <- newPred
  insistOnMintTeaWithFood <- newPred
  john <- PN <$> newInd
  observe $ if_ (cltoS pos (s1 genericYou (modify regularly eatHumus))) (cltoS pos (s1 genericYou (modify also enjoyTabouli)))
  observe $ cltoS pos (s1 (qNP genericPl (relativiseCN person (makepolarRS pos (makeRCL tHAT enjoyTabouli)))) (bare insistOnMintTeaWithFood))
  return $ if_ (cltoS pos (s1 john (modify regularly eatHumus))) (cltoS pos (s1 john (bare insistOnMintTeaWithFood)))
problem 61 = do
  mary <- PN <$> newInd
  kate <- PN <$> newInd
  christine <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n2_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n5_Dig)))) centimeter tall)))
  return $ cltoS pos (s1 christine (bare (testVP tall)))
problem 62 = do
  musician <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP few person) (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP few person) (bare (isA (non musician))))
  return $ and (parens (not (cltoS pos (s1 john (bare (isA musician)))))) (parens (not (cltoS pos (s1 john (bare (isA (non musician)))))))
problem 63 = do
  guitarist <- newPred
  logician <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (testVP tall)))
  observe $ cltoS pos (s1 (qNP few guitarist) (bare (isA logician)))
  return $ and (cltoS pos (s1 john (bare (testVP tall)))) (cltoS pos (s1 (qNP few guitarist) (bare (isA logician))))
problem 64 = do
  musician <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (testVP tall)))
  observe $ cltoS pos (s1 john (bare (isA musician)))
  return $ and (cltoS pos (s1 john (bare (testVP tall)))) (cltoS pos (s1 john (bare (isA musician))))
problem 65 = do
  guitarist <- newPred
  logician <- newPred
  observe $ cltoS pos (s1 (qNP all guitarist) (modify probably (isA logician)))
  return $ cltoS pos (s1 (qNP most guitarist) (bare (isA logician)))
problem 66 = do
  guitarist <- newPred
  logician <- newPred
  observe $ cltoS pos (s1 (qNP all guitarist) (bare (isA logician)))
  return $ cltoS pos (s1 (qNP all guitarist) (modify probably (isA logician)))
problem 67 = do
  guitarist <- newPred
  logician <- newPred
  observe $ cltoS pos (s1 (qNP few guitarist) (bare (isA logician)))
  return $ cltoS pos (s1 (qNP all guitarist) (bare (isA logician)))
problem 68 = do
  guitarist <- newPred
  logician <- newPred
  observe $ cltoS pos (s1 (qNP all guitarist) (modify probably (isA logician)))
  return $ cltoS pos (s1 (qNP all guitarist) (modify probably (isA logician)))
problem 69 = do
  guitarist <- newPred
  logician <- newPred
  observe $ cltoS pos (s1 (qNP all guitarist) (bare (isA logician)))
  return $ cltoS pos (s1 (qNP all guitarist) (bare (isA logician)))
problem 70 = do
  mary <- PN <$> newInd
  kate <- PN <$> newInd
  christine <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n2_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n7_Dig (oneDigit n9_Dig)))) centimeter tall)))
  return $ cltoS pos (s1 christine (bare (testVP tall)))
problem 71 = do
  mary <- PN <$> newInd
  kate <- PN <$> newInd
  christine <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n8_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n9_Dig)))) centimeter tall)))
  return $ not (cltoS neg (s1 christine (bare (testVP tall))))
problem 72 = do
  mary <- PN <$> newInd
  kate <- PN <$> newInd
  christine <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n9_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n8_Dig)))) centimeter tall)))
  return $ cltoS neg (s1 christine (bare (testVP tall)))
problem 73 = do
  mary <- PN <$> newInd
  kate <- PN <$> newInd
  helen <- PN <$> newInd
  christine <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall)))
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 helen (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n7_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 helen (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n5_Dig)))) centimeter tall)))
  return $ cltoS neg (s1 christine (bare (testVP tall)))
problem 74 = do
  kate <- PN <$> newInd
  helen <- PN <$> newInd
  christine <- PN <$> newInd
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 kate (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 kate (bare (testVP tall)))
  observe $ cltoS pos (s1 helen (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n8_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS neg (s1 helen (bare (testVP tall)))
  observe $ cltoS pos (s1 christine (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n9_Dig (oneDigit n0_Dig)))) centimeter tall)))
  return $ cltoS pos (s1 christine (bare (testVP tall)))
problem 75 = do
  basketballPlayer <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 (qNP few person) (bare (isA basketballPlayer)))
  observe $ cltoS pos (s1 (qNP genericPl basketballPlayer) (bare (moreVP tall (qNP most (non basketballPlayer)))))
  observe $ cltoS pos (s1 john (bare (isA basketballPlayer)))
  return $ cltoS pos (s1 john (bare (moreVP tall (qNP many person))))
problem 76 = do
  violinist <- newPred
  musician <- newPred
  readMusic <- newPred
  observe $ cltoS pos (s1 (qNP all violinist) (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP all musician) (bare readMusic))
  return $ cltoS pos (s1 (qNP all violinist) (bare readMusic))
problem 77 = do
  violinist <- newPred
  musician <- newPred
  readMusic <- newPred
  observe $ cltoS pos (s1 (qNP all violinist) (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP all musician) (bare readMusic))
  return $ cltoS pos (s1 (percentOf (digitsToCard (addDigit n9_Dig (oneDigit n9_Dig))) violinist) (bare readMusic))
problem 78 = do
  musician <- newPred
  guitarist <- newPred
  logician <- newPred
  readMusic <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP every guitarist) (bare (isA logician)))
  observe $ if_ (cltoS pos (s1 (qNP every guitarist) (bare (isA logician)))) (cltoS pos (s1 (qNP every musician) (bare readMusic)))
  observe $ cltoS pos (s1 john (bare (isA musician)))
  return $ cltoS pos (s1 john (bare readMusic))
problem 79 = do
  basketballPlayer <- newPred
  john <- PN <$> newInd
  tall <- newMeasure
  observe $ cltoS pos (s1 john (bare (isA basketballPlayer)))
  observe $ cltoS pos (s1 (qNP genericPl basketballPlayer) (bare (moreVP tall (qNP genericPl (non basketballPlayer)))))
  return $ cltoS pos (s1 john (bare (moreVP tall (percentOf (digitsToCard (addDigit n8_Dig (oneDigit n0_Dig))) person))))
problem 80 = do
  bird <- newPred
  animal <- newPred
  fly <- newPred
  observe $ cltoS neg (s1 (qNP most animal) (bare fly))
  observe $ cltoS pos (s1 (qNP most bird) (bare fly))
  observe $ cltoS pos (s1 (qNP every bird) (bare (isA animal)))
  return $ cltoS neg (s1 (qNP most animal) (bare (isA bird)))
problem 81 = do
  bird <- newPred
  fly <- newPred
  observe $ cltoS pos (s1 (qNP most bird) (bare fly))
  return $ cltoS pos (s1 (qNP aFew bird) (bare fly))
problem 82 = do
  musician <- newPred
  logician <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP many logician) (bare (isA musician)))
  observe $ cltoS pos (s1 john (bare (isA logician)))
  return $ cltoS pos (s1 john (bare (isA musician)))
problem 83 = do
  musician <- newPred
  logician <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP many logician) (bare (isA musician)))
  observe $ cltoS pos (s1 john (bare (isA musician)))
  return $ cltoS pos (s1 john (bare (isA logician)))
problem 84 = do
  musician <- newPred
  logician <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP many logician) (bare (isA musician)))
  observe $ cltoS neg (s1 (qNP most person) (bare (isA logician)))
  observe $ cltoS pos (s1 john (bare (isA musician)))
  return $ cltoS pos (s1 john (bare (isA logician)))
input 1 = ["every violinist is a musician","musicians generally read music","if john is a violinist then john reads music"]
input 2 = ["prolog programmers are always intermediate logic students","intermediate logic students rarely read music","prolog programmers don't read music"]
input 3 = ["many bald men are toupee wearers","toupee wearers always try hair transplant treatment","john is a bald man","john tries hair transplant treatment"]
input 4 = ["john is a basketball player","basketball players are usually taller than non basketball players","john is taller than most people"]
input 5 = ["john is a short basketball player","basketball players are usually less short than non basketball players","john is short"]
input 6 = ["all basketball players are probably tall","most basketball players are tall"]
input 7 = ["4 &+ 0 percent of prolog programmers read music","violinists don't like prolog programmers that read music","violinists don't like most prolog programmers"]
input 8 = ["prolog programmers definitely use tail recursion","many logicians are prolog programmers","logicians use tail recursion"]
input 9 = ["stones fans often prefer the doors to the beatles","john is a stones fan","john prefers the doors to the beatles"]
input 10 = ["if you play for the leafs then you are probably traded from the canadiens","if you are traded from the canadiens then you often play in the montreal forum","john plays for the leafs","john plays in the montreal forum"]
input 11 = ["turkish coffee drinkers frequently enjoy a shot of arak","most people that enjoy a shot of arak also listen to classical oud music","turkish coffee drinkers listen to classical oud music"]
input 12 = ["if you regularly eat humus then you also enjoy tabouli","most people that enjoy tabouli insist on having mint tea with food","if you eat humus then you insist on having mint tea with food"]
input 13 = ["cricket players rarely hit a home run","mary hits a home run","mary isn't a cricket player"]
input 14 = ["many jazz guitarists can play more than 1 &+ 0 &+ 0 chords","few violinists can play more than 1 &+ 0 chords","john can play more than 8 &+ 0 chords","john is a jazz guitarist"]
input 15 = ["mary is tall","john is taller than mary","john is tall"]
input 16 = ["mary isn't tall","mary is taller than john","john isn't tall"]
input 17 = ["john is always as punctual as mary","sam is usually more punctual than john","sam is more punctual than mary"]
input 18 = ["many linguists know formal language theory","most linguists that know formal language theory dislike experimental work","many linguists dislike experimental work"]
input 19 = ["most conservatives don't usually support free university education","john supports free university education","john isn't a conservative"]
input 20 = ["if you are a guitarist then you are probably a stones fan","if you are a stones fan then you generally prefer the doors to the beatles","it is not the case that every person that doesn't prefer the doors to the beatles is a person that isn't a guitarist"]
input 21 = ["if you are a guitarist then you are probably a stones fan","if you are a stones fan then you generally prefer the doors to the beatles","every person that doesn't prefer the doors to the beatles isn't a guitarist"]
input 22 = ["8 &+ 0 percent of basketball players are tall","basketball players are probably tall"]
input 23 = ["8 &+ 0 percent of basketball players are tall","few basketball players aren't tall"]
input 24 = ["prolog programmers definitely use tail recursion","logicians are frequently prolog programmers","logicians probably use tail recursion"]
input 25 = ["john is tall","all guitarists are logicians","john is tall and all guitarists are logicians"]
input 26 = ["john is tall","all guitarists are logicians","john is tall"]
input 27 = ["john is taller than mary","john is tall"]
input 28 = ["john is taller than mary","mary is taller than sam","john is taller than molly"]
input 29 = ["john is taller than mary","sam is taller than mary","kate is taller than christine","kate is taller than john"]
input 30 = ["all intermediate logic students are stones fans","john is an intermediate logic student","john is a stones fan"]
input 31 = ["john is a guitarist","most guitarists aren't logicians","john isn't a logician"]
input 32 = ["john is a logician","most guitarists aren't logicians","john isn't a guitarist"]
input 33 = ["it is not the case that john is taller than most people"]
input 34 = ["a few people are shorter than john"]
input 35 = ["it is not the case that few people are shorter than john"]
input 36 = ["john isn't a guitarist","it is not the case that john is a guitarist"]
input 37 = ["mary is 1 &+ 9 &+ 0 centimeters tall","mary is tall","molly is 1 &+ 8 &+ 4 centimeters tall","molly is tall","ruth is 1 &+ 8 &+ 0 centimeters tall","ruth is tall","helen is 1 &+ 7 &+ 8 centimeters tall","helen is tall","athena is 1 &+ 6 &+ 6 centimeters tall","athena isn't tall","artemis is 1 &+ 5 &+ 7 centimeters tall","artemis isn't tall","joanna is 1 &+ 6 &+ 0 centimeters tall","joanna isn't tall","kate is 1 &+ 6 &+ 2 centimeters tall","kate isn't tall","christine is 1 &+ 7 &+ 8 centimeters tall","christine is tall"]
input 38 = ["mary is 1 &+ 8 &+ 9 centimeters tall","mary is tall","molly is 1 &+ 8 &+ 4 centimeters tall","molly is tall","ruth is 1 &+ 8 &+ 0 centimeters tall","ruth is tall","helen is 1 &+ 7 &+ 8 centimeters tall","helen is tall","athena is 1 &+ 6 &+ 6 centimeters tall","athena isn't tall","artemis is 1 &+ 5 &+ 7 centimeters tall","artemis isn't tall","joanna is 1 &+ 6 &+ 0 centimeters tall","joanna isn't tall","kate is 1 &+ 6 &+ 2 centimeters tall","kate isn't tall","christine is 1 &+ 6 &+ 3 centimeters tall","christine isn't tall"]
input 39 = ["many jazz guitarists can play more than 2 chords","few violinists can play more than 1 chord","john can play more than 2 chords","john is a jazz guitarist"]
input 40 = ["many jazz guitarists can play more than 5 chords","few violinists can play more than 2 chords","john can play more than 4 chords","john is a jazz guitarist"]
input 41 = ["john is 1 &+ 8 &+ 0 centimeters tall","john is 6 foot tall","mary is 6 foot tall","mary is 1 &+ 8 &+ 0 centimeters tall"]
input 42 = ["mary is 1 &+ 9 &+ 0 centimeters tall","mary is tall","molly is 1 &+ 8 &+ 4 centimeters tall","molly is tall","ruth is 1 &+ 8 &+ 0 centimeters tall","ruth is tall","helen is 1 &+ 7 &+ 8 centimeters tall","helen is tall","athena is 1 &+ 6 &+ 6 centimeters tall","athena isn't tall","artemis is 1 &+ 5 &+ 7 centimeters tall","artemis isn't tall","joanna is 1 &+ 6 &+ 0 centimeters tall","joanna isn't tall","kate is 1 &+ 6 &+ 2 centimeters tall","kate isn't tall","christine is 1 &+ 7 &+ 1 centimeters tall","( it is not the case that christine is tall ) and ( it is not the case that christine isn't tall )"]
input 43 = ["john is taller than mary","john is 1 &+ 8 &+ 5 centimeters tall","mary is 5 foot tall","1 &+ 8 &+ 5 centimeters is more than 5 foot"]
input 44 = ["john is taller than mary","mary is 5 foot tall","john is more than 5 foot tall"]
input 45 = ["john is a guitarist","guitarists are kind of musicians","john is a musician"]
input 46 = ["john is a guitarist","guitarists are pretty much musicians","john is a musician"]
input 47 = ["john is a basketball player","basketball players are tall","john is taller than 5 &+ 0 percent of people"]
input 48 = ["many jazz guitarists can play more than 1 &+ 0 &+ 0 chords","few violinists can play more than 1 &+ 0 chords","john can play more than 8 &+ 0 chords","john isn't a violinist"]
input 49 = ["many jazz guitarists can play more than 1 &+ 0 &+ 0 chords","few violinists can play more than 1 &+ 0 chords","john can play less than 1 &+ 5 chords","john is a violinist"]
input 50 = ["many jazz guitarists can play more than 1 &+ 0 &+ 0 chords","few violinists can play more than 1 &+ 0 chords","john can play more than 9 &+ 0 chords","john is a jazz guitarist"]
input 51 = ["jazz guitarists are musicians","violinists are musicians","john is a musician","many jazz guitarists can play more than 1 &+ 0 &+ 0 chords","few violinists can play more than 1 &+ 0 chords","john can play more than 9 &+ 0 chords","john is a jazz guitarist"]
input 52 = ["jazz guitarists are musicians","violinists are musicians","john is a musician","musicians can play more than 1 chord","many jazz guitarists can play more than 1 &+ 0 &+ 0 chords","few violinists can play more than 1 &+ 0 chords","john can play more than 9 &+ 0 chords","john is a jazz guitarist"]
input 53 = ["john is a basketball player","basketball players are taller than most non basketball players","john is taller than most non basketball players"]
input 54 = ["few people are basketball players","basketball players are taller than most non basketball players","john is a basketball player","john is taller than most people"]
input 55 = ["9 &+ 9 percent of people are non basketball players","basketball players are taller than most non basketball players","john is a basketball player","john is taller than most people"]
input 56 = ["if you regularly eat humus then you also enjoy tabouli","people that enjoy tabouli insist on having mint tea with food","if you regularly eat humus then you insist on having mint tea with food"]
input 57 = ["if you eat humus then you also enjoy tabouli","people that enjoy tabouli insist on having mint tea with food","if you eat humus then you insist on having mint tea with food"]
input 58 = ["if you eat humus then you also enjoy tabouli","john eats humus","john enjoys tabouli"]
input 59 = ["if you eat humus then you also enjoy tabouli","people that enjoy tabouli insist on having mint tea with food","if john eats humus then john insists on having mint tea with food"]
input 60 = ["if you regularly eat humus then you also enjoy tabouli","people that enjoy tabouli insist on having mint tea with food","if john regularly eats humus then john insists on having mint tea with food"]
input 61 = ["mary is 1 &+ 9 &+ 0 centimeters tall","mary is tall","kate is 1 &+ 6 &+ 2 centimeters tall","kate isn't tall","christine is 1 &+ 8 &+ 5 centimeters tall","christine is tall"]
input 62 = ["few people are musicians","few people are non musicians","( it is not the case that john is a musician ) and ( it is not the case that john is a non musician )"]
input 63 = ["john is tall","few guitarists are logicians","john is tall and few guitarists are logicians"]
input 64 = ["john is tall","john is a musician","john is tall and john is a musician"]
input 65 = ["all guitarists are probably logicians","most guitarists are logicians"]
input 66 = ["all guitarists are logicians","all guitarists are probably logicians"]
input 67 = ["few guitarists are logicians","all guitarists are logicians"]
input 68 = ["all guitarists are probably logicians","all guitarists are probably logicians"]
input 69 = ["all guitarists are logicians","all guitarists are logicians"]
input 70 = ["mary is 1 &+ 9 &+ 0 centimeters tall","mary is tall","kate is 1 &+ 6 &+ 2 centimeters tall","kate isn't tall","christine is 1 &+ 7 &+ 9 centimeters tall","christine is tall"]
input 71 = ["mary is 1 &+ 9 &+ 0 centimeters tall","mary is tall","kate is 1 &+ 8 &+ 8 centimeters tall","kate isn't tall","christine is 1 &+ 8 &+ 9 centimeters tall","it is not the case that christine isn't tall"]
input 72 = ["mary is 1 &+ 9 &+ 0 centimeters tall","mary is tall","kate is 1 &+ 8 &+ 9 centimeters tall","kate isn't tall","christine is 1 &+ 8 &+ 8 centimeters tall","christine isn't tall"]
input 73 = ["mary is 1 &+ 9 &+ 0 centimeters tall","mary is tall","kate is 1 &+ 8 &+ 0 centimeters tall","kate is tall","helen is 1 &+ 7 &+ 0 centimeters tall","helen isn't tall","christine is 1 &+ 6 &+ 5 centimeters tall","christine isn't tall"]
input 74 = ["kate is 1 &+ 9 &+ 0 centimeters tall","kate is tall","helen is 1 &+ 8 &+ 0 centimeters tall","helen isn't tall","christine is 1 &+ 9 &+ 0 centimeters tall","christine is tall"]
input 75 = ["few people are basketball players","basketball players are taller than most non basketball players","john is a basketball player","john is taller than many people"]
input 76 = ["all violinists are musicians","all musicians read music","all violinists read music"]
input 77 = ["all violinists are musicians","all musicians read music","9 &+ 9 percent of violinists read music"]
input 78 = ["every guitarist is a logician","if every guitarist is a logician then every musician reads music","john is a musician","john reads music"]
input 79 = ["john is a basketball player","basketball players are taller than non basketball players","john is taller than 8 &+ 0 percent of people"]
input 80 = ["most animals don't fly","most birds fly","every bird is an animal","most animals aren't birds"]
input 81 = ["most birds fly","a few birds fly"]
input 82 = ["many logicians are musicians","john is a logician","john is a musician"]
input 83 = ["many logicians are musicians","john is a musician","john is a logician"]
input 84 = ["many logicians are musicians","most people aren't logicians","john is a musician","john is a logician"]
tags  1 = [["probable inference"],["quantifier"],["modal adverb"]]
tags  2 = [["probable inference"],["quantifier"],["modal adverb"]]
tags  3 = [["probable inference"],["quantifier"],["modal adverb"]]
tags  4 = [["unclear (world knowledge)"],["comparative adjective"],["modal adverb"]]
tags  5 = [["unclear (world knowledge)"],["comparative adjective"],["modal adverb"],["subsectivity"]]
tags  6 = [["probable inference"],["quantifier"],["modal adverb"]]
tags  7 = [["improbable inference"],["percentage determiner"],["modal adverb"],["negation"],["binary predicate"]]
tags  8 = [["probable inference"],["quantifier"],["modal adverb"]]
tags  9 = [["probable inference"],["quantifier"],["temporal adverb"]]
tags  10 = [["probable inference"],["quantifier"],["modal adverb"],["temporal adverb"]]
tags  11 = [["probable inference"],["quantifier"],["temporal adverb"]]
tags  12 = [["probable inference"],["quantifier"],["temporal adverb"]]
tags  13 = [["probable inference"],["quantifier"],["temporal adverb"],["negation"]]
tags  14 = [["unclear"],["quantifiers"]]
tags  15 = [["entailment"],["comparative adjective"],["transitivity"]]
tags  16 = [["entailment"],["comparative adjective"],["transitivity"]]
tags  17 = [["probable inference"],["quantifier"],["modal/temporal adverb"]]
tags  18 = [["probable inference"],["quantifier"]]
tags  19 = [["probable inference"],["quantifier"],["modal/temporal adverb"],["negation"]]
tags  20 = [["probable inference"],["modal adverbs"],["quantifies"],["relative clause"],["negation"],["conditional"],["comment: because the negation is in the relative clause"],["it acts with a narrow scope"],["see also 21 for wide scope"]]
tags  21 = [["probable inference"],["modal adverbs"],["quantifies"],["relative clause"],["negation"],["conditional"]]
tags  22 = [["probable inference"],["percentage determiner"],["modal adverb"]]
tags  23 = [["probable inference"],["percentage determiner"],["negation"]]
tags  24 = [["probable inference"],["quantifier"],["modal adverb"]]
tags  25 = [["fol validity"],["conjunction"]]
tags  26 = [["fol validity"],["weakening"]]
tags  27 = [["probable inference"],["comparative adjective"]]
tags  28 = [["probable inference"],["comparative adjective"],["transitivity"]]
tags  29 = [["probable inference"],["comparative adjective"]]
tags  30 = [["fol validity"],["quantifier"]]
tags  31 = [["probable inference"],["negation"],["modus ponens"]]
tags  32 = [["probable inference"],["negation"],["modus tollens"]]
tags  33 = [["probable inference"],["law of great numbers (object)"],["negation"]]
tags  34 = [["probable inference"],["law of great numbers (subject)"]]
tags  35 = [["probable inference"],["law of great numbers (subject)"],["negation"]]
tags  36 = [["fol validity"],["wide-scope negation"]]
tags  37 = [["entailment"],["positive adjectives"],["vagueness"],["runs","100"]]
tags  38 = [["entailment"],["positive adjectives"],["vagueness"],["runs","100"]]
tags  39 = [["unclear"],["quantifiers"]]
tags  40 = [["unclear"],["quantifiers"]]
tags  41 = [["entailment"],["comparative"],["measure"],["iterations","1000000"]]
tags  42 = [["fol contradiction"],["positive adjectives"],["vagueness"]]
tags  43 = [["entailment"],["comparative"],["measure"],["noparse"]]
tags  44 = [["entailment"],["comparative"],["measure"],["noparse"]]
tags  45 = [["probable inference"],["generalised vagueness"],["noun modifier"],["noparse"]]
tags  46 = [["probable inference"],["generalised vagueness"],["noun modifier"],["noparse"]]
tags  47 = [["probable inference"],["comparative adjective"],["modal adverb"],["percentage determiner"]]
tags  48 = [["probable inference"],["quantifiers"]]
tags  49 = [["unclear"],["quantifiers"]]
tags  50 = [["unclear"],["quantifiers"]]
tags  51 = [["unclear"],["quantifiers"]]
tags  52 = [["unclear"],["quantifiers"]]
tags  53 = [["probable inference"],["comparative adjective"],["modal adverb"]]
tags  54 = [["probable inference"],["comparative adjective"],["modal adverb"]]
tags  55 = [["probable inference"],["comparative adjective"],["modal adverb"],["percentage determiner"]]
tags  56 = [["probable inference"],["quantifier"],["temporal adverb"]]
tags  57 = [["probable inference"],["transitivity of implication"],["comment: doesn't work with planes"],["because the generic plural isn't transitive even combined with optimized universal"]]
tags  58 = [["probable inference"],["modus ponens"]]
tags  59 = [["probable inference"],["transitivity of implication"]]
tags  60 = [["probable inference"],["transitivity of implication"]]
tags  61 = [["probable inference"],["positive adjectives"],["vagueness"],["runs","100"]]
tags  62 = [["fol contradiction"],["comparative adjective"],["grey area"]]
tags  63 = [["fol validity"],["conjunction"],["quantifiers"]]
tags  64 = [["fol validity"],["conjunction"]]
tags  65 = [["probable inference"],["quantifiers"],["modal adverb"]]
tags  66 = [["entailment"],["quantifier"],["modal adverb"]]
tags  67 = [["contradiction"],["quantifiers"]]
tags  68 = [["fol validity"],["quantifier"],["modal adverb"]]
tags  69 = [["fol validity"],["quantifier"]]
tags  70 = [["probable inference"],["positive adjectives"],["vagueness"],["runs","100"]]
tags  71 = [["unclear"],["negative adjectives"],["vagueness"],["runs","100"]]
tags  72 = [["entailment"],["positive adjectives"],["vagueness"],["runs","100"]]
tags  73 = [["entailment"],["negative adjectives"],["vagueness"],["runs","100"]]
tags  74 = [["entailment"],["vagueness"],["runs","100"]]
tags  75 = [["probable inference"],["comparative adjective"],["modal adverb"]]
tags  76 = [["fol validity"],["quantifiers"]]
tags  77 = [["entailment"],["quantifiers"],["percentage determiner"]]
tags  78 = [["fol validity"],["implication"],["quantifier"]]
tags  79 = [["unclear"],["comparative adjective"],["modal adverb"],["percentage determiner"]]
tags  80 = [["probable inference"],["quantifiers"]]
tags  81 = [["entailment"],["quantifiers"]]
tags  82 = [["probable inference"],["quantifier"]]
tags  83 = [["unclear"],["quantifier"]]
tags  84 = [["unclear"],["quantifiers"]]
numberOfProblems = 84
