module Testsuite where

import Lib (observe,P,run,Prop)
import Lib2

problem1 :: P Prop
problem1 = do
  musician <- newPred
  violinist <- newPred
  readMusic <- newPred
  john <- PN <$> newInd
  return $ cltoS pos (s1 (qNP every violinist) (bare (isA musician))) --> cltoS pos (s1 (qNP genericPl musician) (modify generally readMusic)) --> if_ (cltoS pos (s1 john (bare (isA violinist)))) (cltoS pos (s1 john (bare readMusic)))
  
problem2 :: P Prop
problem2 = do
  prologProgrammer <- newPred
  interLogicStudent <-newPred
  readMusic <- newPred
  
  return $ cltoS pos (s1 (qNP genericPl prologProgrammer) (modify always (isA interLogicStudent))) --> cltoS pos (s1 (qNP genericPl interLogicStudent) (modify rarely readMusic)) --> cltoS neg (s1 (qNP genericPl prologProgrammer) (bare readMusic))


main :: IO ()
main = run problem2

-- problem2 = cltoS pos (s1 (qNP genericPl prologProgrammer) (modify always (isA interLogicStudent))) --> cltoS pos (s1 (qNP genericPl interLogicStudent) (modify rarely readMusic)) --> cltoS neg (s1 (qNP genericPl prologProgrammer) (bare readMusic))
-- problem3 = cltoS pos (s1 (qNP many baldMan) (bare (isA toupeeWearer))) --> cltoS pos (s1 (qNP genericPl toupeeWearer) (modify always tryHairTransplantTreatment)) --> cltoS pos (s1 john (bare (isA baldMan))) --> cltoS pos (s1 john (bare tryHairTransplantTreatment))
-- problem4 = cltoS pos (s1 john (bare (isA basketballPlayer))) --> cltoS pos (s1 (qNP genericPl basketballPlayer) (modify usually (comparVP more tall (qNP genericPl (non basketballPlayer))))) --> cltoS pos (s1 john (bare (comparVP more tall (qNP most person))))
-- problem5 = cltoS pos (s1 john (bare (isA (qual short basketballPlayer)))) --> cltoS pos (s1 (qNP genericPl basketballPlayer) (modify usually (comparVP more tall (qNP genericPl (non basketballPlayer))))) --> cltoS pos (s1 john (bare (testVP short)))
-- problem6 = cltoS pos (s1 (qNP all basketballPlayer) (modify probably (testVP tall))) --> cltoS pos (s1 (qNP most basketballPlayer) (bare (testVP tall)))
-- problem7 = cltoS pos (s1 (percentOf forty prologProgrammer) (bare readMusic)) --> cltoS neg (s1 (qNP genericPl violinist) (bare (like (qNP genericPl (relativiseCN prologProgrammer (makepolarRS pos (makeRCL tHAT readMusic))))))) --> cltoS neg (s1 (qNP genericPl violinist) (bare (like (qNP most prologProgrammer))))
-- problem8 = cltoS pos (s1 (qNP genericPl prologProgrammer) (modify definitely useTailRec)) --> cltoS pos (s1 (qNP many logician) (bare (isA prologProgrammer))) --> cltoS pos (s1 (qNP genericPl logician) (bare useTailRec))
-- problem9 = cltoS pos (s1 (qNP genericPl stonesFan) (modify often preferTheDoorsToTheBeatles)) --> cltoS pos (s1 john (bare (isA stonesFan))) --> cltoS pos (s1 john (bare preferTheDoorsToTheBeatles))
-- problem10 = if_ (cltoS pos (s1 genericYou (bare playForTheLeafs))) (cltoS pos (s1 genericYou (modify probably (testVP tradedFromTheCanadiens)))) --> if_ (cltoS pos (s1 genericYou (bare (testVP tradedFromTheCanadiens)))) (cltoS pos (s1 genericYou (modify often playInMF))) --> cltoS pos (s1 john (bare playForTheLeafs)) --> cltoS pos (s1 john (bare playInMF))
-- problem11 = cltoS pos (s1 (qNP genericPl turkishCoffeeDrinker) (modify frequently enjoyArak)) --> cltoS pos (s1 (qNP most (relativiseCN person (makepolarRS pos (makeRCL tHAT enjoyArak)))) (modify also listenToOudMusic)) --> cltoS pos (s1 (qNP genericPl turkishCoffeeDrinker) (bare listenToOudMusic))
-- problem12 = if_ (cltoS pos (s1 genericYou (modify regularly eatHumus))) (cltoS pos (s1 genericYou (modify also enjoyTabouli))) --> cltoS pos (s1 (qNP most (relativiseCN person (makepolarRS pos (makeRCL tHAT enjoyTabouli)))) (bare insistOnMintTeaWithFood)) --> if_ (cltoS pos (s1 genericYou (bare eatHumus))) (cltoS pos (s1 genericYou (bare insistOnMintTeaWithFood)))
-- problem13 = cltoS pos (s1 (qNP genericPl baseballPlayer) (modify occasionally hitRun)) --> cltoS pos (s1 (qNP genericPl cricketPlayer) (modify never hitRun)) --> cltoS pos (s1 mary (bare hitRun)) --> but (cltoS pos (s1 mary (bare (isA baseballPlayer)))) (cltoS neg (s1 mary (bare (isA cricketPlayer))))
-- problem14 = cltoS pos (s1 (qNP many jazzGuitarist) (bare (canPlayChoords (atLeast oneHundred)))) --> cltoS pos (s1 (qNP few violinist) (bare (canPlayChoords (moreThan ten)))) --> cltoS pos (s1 john (bare (canPlayChoords (exactly eighty)))) --> cltoS pos (s1 john (bare (isA jazzGuitarist)))
-- problem15 = cltoS pos (s1 (qNP few introLogicStudent) (bare canProveFOL)) --> cltoS pos (s1 (qNP many interLogicStudent) (bare canProveFOL)) --> cltoS pos (s1 molly (bare canProveFOL)) --> cltoS pos (s1 molly (bare (isA interLogicStudent)))
-- problem16 = cltoS pos (s1 (qNP few introLogicStudent) (bare canProveFOL)) --> cltoS pos (s1 (qNP most advanLogicStudent) (bare canProveFOL)) --> cltoS pos (s1 molly (bare canProveFOL)) --> cltoS pos (s1 molly (bare (isA advanLogicStudent)))
-- problem17 = cltoS pos (s1 john (modify always (comparVP equal punctual mary))) --> cltoS pos (s1 sam (modify usually (comparVP more punctual john))) --> cltoS pos (s1 sam (bare (comparVP more punctual mary)))
-- problem18 = cltoS pos (s1 (qNP many linguist) (bare knowFLT)) --> cltoS pos (s1 (qNP most (relativiseCN linguist (makepolarRS pos (makeRCL tHAT knowFLT)))) (bare dislikeExperimentalWork)) --> cltoS pos (s1 (qNP many linguist) (bare dislikeExperimentalWork))
