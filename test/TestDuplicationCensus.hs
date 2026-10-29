{-# LANGUAGE ScopedTypeVariables #-}
-- | The duplication census (docs-repo design @ir-duplication-census@,
-- "SPLL.DuplicationCensus"): its keying, and the tripwires built on it.
--
-- * 'duplicationCensusUnitTests': what counts as one subtree.
-- * 'duplicationGrowthTests': the copy count M on the three families whose
--   blowups the repeated-computation audit found, at a few small sizes.
-- * 'duplicationCensusSweep': the corpus ratchet over every program's -O0 IR,
--   against the pins in 'duplicationPinsFile'.
module TestDuplicationCensus
  ( duplicationCensusUnitTests
  , duplicationGrowthTests
  , duplicationCensusSweep
  , duplicationPinsFile
  , pairCeiling
  ) where

import Control.Exception (SomeException, evaluate, try)
import Data.List (sortOn)
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, testCaseInfo, assertBool, assertEqual, assertFailure)

import CorpusSweep
import SPLL.IntermediateRepresentation
import SPLL.CompilerConfig
import SPLL.Lang.Types (GenericValue(..), CompilerError)
import SPLL.DuplicationCensus
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude (compile)

-- | A closed arithmetic chain of @2n+1@ nodes over its argument.
chain :: Int -> IRExpr -> IRExpr
chain 0 e = e
chain n e = IROp OpPlus (chain (n - 1) e) (IRConst (VFloat (fromIntegral n)))

-- | @let v = chain 20 (const 0) in chain 20 v@: about 80 nodes, binding @v@.
letBlock :: Varname -> IRExpr
letBlock v = IRLetIn v (chain 20 (IRConst (VFloat 0))) (chain 20 (IRVar v))

copiesIn :: IRExpr -> Int
copiesIn e = maybe 1 dupCount (case duplicatesIn defaultMinSize e of { (d : _) -> Just d; [] -> Nothing })

duplicationCensusUnitTests :: TestTree
duplicationCensusUnitTests = testGroup "DuplicationCensus"
  [ testCase "two compiles of one expression, with different fresh binders, are one subtree" $
      assertEqual "copies" 2 (copiesIn (IROp OpPlus (letBlock "l_1_x") (letBlock "l_7_x")))
  , testCase "the same text reading two different free variables is two subtrees" $
      assertEqual "copies" 1 (copiesIn (IROp OpPlus (chain 20 (IRVar "l_1_y")) (chain 20 (IRVar "l_2_y"))))
  , testCase "a subtree binding a name does not merge with one reading it from outside" $
      -- (lambda x. chain x) next to (lambda z. chain x): the two chains are one
      -- subtree (each reads x freely), the two lambdas are not
      let bound = IRLambda "x" (chain 20 (IRVar "x"))
          free  = IRLambda "z" (chain 20 (IRVar "x"))
          sizes = [ dupSize d | d <- duplicatesIn defaultMinSize (IROp OpPlus bound free) ]
      in assertEqual "largest duplicated subtree" 41 (maximum sizes)
  , testCase "a binder's de Bruijn index tells nested binders apart" $
      let inner v w r = IRLambda v (IRLambda w (chain 20 (IRVar r)))
      in do
        assertEqual "outer read" 1 (copiesIn (IROp OpPlus (inner "a" "b" "a") (inner "c" "d" "d")))
        assertEqual "same read" 2 (copiesIn (IROp OpPlus (inner "a" "b" "a") (inner "c" "d" "c")))
  , testCase "copies inside copies multiply" $
      let twice e = IROp OpPlus e e
      in assertEqual "copies" 4 (copiesIn (twice (IRLetIn "u" (twice (letBlock "l_3_x")) (IRVar "u"))))
  , testCase "subtrees below the size threshold are not counted" $
      assertEqual "copies" 1 (copiesIn (IROp OpPlus (chain 5 (IRVar "y")) (chain 5 (IRVar "y"))))
  , testCase "fresh-name tags name the building site" $
      assertEqual "tags" ["open_body", "mat_leaf"]
        (freshNameTags (IRLetIn "l_4_open_body" (IRVar "l_9_open_body") (IRVar "l_12_l_3_mat_leaf")))
  ]

-- | M of main's probability body, at -O0.
mainProbCopies :: String -> IO Int
mainProbCopies src = case tryParseProgram "census" src of
  Left err -> assertFailure ("parse error: " ++ show err) >> return 0
  Right prog -> case compile defaultCompilerConfig { optimizerLevel = 0, noIntegrate = True } prog of
    Left e -> assertFailure ("compile error: " ++ e) >> return 0
    Right env -> case [ c | c <- censusEnv defaultMinSize env, fcGroup c == "main", fcVariant c == "prob" ] of
      [c] -> return (maxCopies c)
      _ -> assertFailure "no main probability body" >> return 0

-- | The three families of the repeated-computation audit, each with a point
-- fix. A row's bounds are today's values, so a new fan-out on these shapes
-- fails too. Checked once by reverting each fix (on 360fd08):
--
-- * the acc_imposs binding (field-constructor-prune-guard-exponential-in-width):
--   M = 6 / 30 / 126 at N = 2 / 4 / 6, this row red, and 27 corpus programs;
-- * the constant ANY arm (anyexcept-any-arm-compiled-instead-of-constant):
--   M = 2 / 3 / 9 at d = 2 / 3 / 4, this row red, and 6 corpus programs;
-- * the shared open body (witness-fold-open-body-copied-per-field): 22 corpus
--   programs red, but not this row. Its M is set by the still-open
--   witness-fold-wildcard-body-compiled-twice (4 / 44 / 258 at K = 2 / 3 / 4,
--   copies of a 33-node closed ANY test), which the revert barely moves
--   (4 / 40 / 250). Lower the bound when that task lands.
duplicationGrowthTests :: TestTree
duplicationGrowthTests = testGroup "DuplicationGrowth"
  [ family "independent single-use lets (witness-fold-open-body-copied-per-field)" indepLets [(2, 4), (3, 44)]
  , family "N-field constructor (field-constructor-prune-guard-exponential-in-width)" wideCtor [(2, 2), (4, 4), (6, 4)]
  , family "nested == True (anyexcept-any-arm-compiled-instead-of-constant)" eqChain [(1, 1), (2, 2), (3, 2), (4, 2)]
  ]
  where
    family :: String -> (Int -> String) -> [(Int, Int)] -> TestTree
    family name gen rows = testCase name $ mapM_ (\(k, bound) -> do
        m <- mainProbCopies (gen k)
        assertBool ("size " ++ show k ++ ": M = " ++ show m ++ ", bound " ++ show bound) (m <= bound)) rows
    indepLets k = "main = " ++ concat [ "draw x" ++ show i ++ " = Normal in " | i <- [1 .. k] ]
                  ++ foldr1 (\a b -> "(" ++ a ++ ", " ++ b ++ ")") [ "x" ++ show i | i <- [1 .. k] ] ++ "\n"
    wideCtor n = unlines
      [ "data R = R " ++ concat [ "f" ++ show i ++ "::Int, " | i <- [1 .. n] ] ++ "g::Int"
      , ""
      , "main = R " ++ unwords (map show [1 .. n]) ++ " (if Uniform < 0.5 then 1 else 2)" ]
    eqChain d = "main = " ++ iterate (\e -> "(" ++ e ++ " == True)") "(Uniform < 0.5)" !! d ++ "\n"

-- ---------------------------------------------------------------------------
-- The corpus ratchet.

-- | The checked-in pins: one line per corpus program that has a function body
-- whose M exceeds 'pairCeiling', listing every such body with its M.
duplicationPinsFile :: FilePath
duplicationPinsFile = "test/duplication-census-pins.txt"

-- | The M every body not in the pin file may reach: a pair (a then- and an
-- else-arm, a CDF and its point mass) is ordinary, a third copy is pinned.
pairCeiling :: Int
pairCeiling = 2

-- | @program -> [(group.variant, M)]@.
type Pins = Map.Map String [(String, Int)]

parsePins :: String -> Either String Pins
parsePins txt = do
  rows <- mapM row [ (i, ws) | (i, l) <- zip [1 :: Int ..] (lines txt), let ws = words (takeWhile (/= '#') l), not (null ws) ]
  let dups = [ n | (n, k) <- Map.toList (Map.fromListWith (+) [ (n, 1 :: Int) | (n, _) <- rows ]), k > 1 ]
  if null dups then Right (Map.fromList rows) else Left ("programs pinned twice: " ++ unwords dups)
  where
    row (i, prog : fs) = (,) prog <$> mapM (field i) fs
    row (i, []) = Left ("line " ++ show i ++ ": empty")
    field i f = case break (== '=') f of
      (body, '=' : m) | not (null body), [(v, "")] <- reads m, v > pairCeiling -> Right (body, v)
      _ -> Left ("line " ++ show i ++ ": expected group.variant=M with M > " ++ show pairCeiling ++ ", got " ++ show f)

-- | The pin line of a program's census, or 'Nothing' when every body is
-- within 'pairCeiling'.
pinLine :: String -> [FunctionCensus] -> Maybe String
pinLine name fcs = case [ (bodyName c, maxCopies c) | c <- fcs, maxCopies c > pairCeiling ] of
  [] -> Nothing
  rs -> Just (unwords (name : [ b ++ "=" ++ show m | (b, m) <- sortOn fst rs ]))

bodyName :: FunctionCensus -> String
bodyName c = fcGroup c ++ "." ++ fcVariant c

-- | One test per corpus program, on the -O0 compile the caller already holds
-- (End2End's, shared with "Interpreter Unoptimized", so no compile is added
-- for a program that sweep runs). The @slow@ programs are censused too, bar
-- 'slowForCompileCost': the census needs only their -O0 compile, about 20 s
-- of CPU for the ~520 of them, which the default tier can afford (it is the
-- larger part of the corpus). Each program:
-- every function body's M is exactly its pin, or at most 'pairCeiling' if it
-- has none. A body above its pin is a new copy fan-out and fails with the
-- subtree; a body below its pin fails too, so a pin goes down in the same
-- commit as the fix that lowers it. A program that does not compile has
-- nothing to count and passes.
duplicationCensusSweep :: Corpus -> String -> (CorpusEntry -> Either CompilerError IREnv) -> IO TestTree
duplicationCensusSweep corpus path unopt = do
  pinsE <- parsePins <$> readFile duplicationPinsFile
  let pins = either (\e -> error (duplicationPinsFile ++ ": " ++ e)) id pinsE
  corpusSweepAll corpus SweepSpec
    { sweepName = path ++ ".DuplicationCensus", sweepTier = Default, sweepSlow = IgnoreSlow
    , sweepSelect = notSlowForCompileCost
    , sweepNote = "each -O0 function body's copy count of its most-copied subtree is its pin, or at most a pair" } $ \es ->
      return $ testGroup "DuplicationCensus" $
        testCase "the pin file names only censused corpus programs"
          (assertEqual "pinned programs the sweep does not see" [] (Map.keys pins `minus` map ceName es))
        : [ testCaseInfo (ceName e) (checkProgram (Map.lookup (ceName e) pins) e) | e <- es ]
  where
    minus xs ys = filter (`notElem` ys) xs
    checkProgram pinned e = do
      r <- try (evaluate (forceCensus (either (const Nothing) (Just . censusEnv defaultMinSize) (unopt e))))
      case r of
        Left (ex :: SomeException) -> return ("compile raised, nothing to count: " ++ takeWhile (/= '\n') (show ex))
        Right Nothing -> return "does not compile, nothing to count"
        Right (Just fcs) -> do
          let pinOf b = pinned >>= lookup b
              verdict c = let b = bodyName c; m = maxCopies c
                          in case pinOf b of
                               Just p | m > p -> Just (Left (b, m, Just p, c))
                                      | m < p -> Just (Right (b, m, p))
                               Nothing | m > pairCeiling -> Just (Left (b, m, Nothing, c))
                               _ -> Nothing
              verdicts = [ v | c <- fcs, Just v <- [verdict c] ]
              rises = [ x | Left x <- verdicts ]
              falls = [ x | Right x <- verdicts ]
              gone = [ b | (b, _) <- fromMaybe [] pinned, b `notElem` map bodyName fcs ]
              newLine = fromMaybe ("(remove the line: every body is within " ++ show pairCeiling ++ ")") (pinLine (ceName e) fcs)
          if null rises && null falls && null gone
            then return ("M = " ++ show (maximum (1 : map maxCopies fcs)))
            else assertFailure $ unlines $
              [ b ++ ": M = " ++ show m ++ " above " ++ maybe ("the pair ceiling " ++ show pairCeiling) (\q -> "its pin " ++ show q) p
                  ++ " -- a new copy fan-out (design ir-duplication-census). The most-copied subtree:\n" ++ renderCensus defaultMinSize 1 [c]
              | (b, m, p, c) <- rises ]
              ++ [ b ++ ": M = " ++ show m ++ ", below its pin " ++ show p ++ ": lower the pin in this commit" | (b, m, p) <- falls ]
              ++ [ b ++ ": pinned, but the program has no such body any more" | b <- gone ]
              ++ [ "If the change is intended, the line in " ++ duplicationPinsFile ++ " becomes:", "  " ++ newLine ]
    forceCensus x = case x of
      Nothing -> x
      Just fcs -> sum (map maxCopies fcs) `seq` x
