-- | The pure half of the known-issues performance pins (task
-- known-issues-performance-scaling-checks): expanding a program-family
-- template at one knob value, and deciding from a climb over the family
-- whether a resource still grows faster than a polynomial bound.
-- "TestKnownIssues" does the measuring; everything here is deterministic and
-- unit-tested by 'scalingCheckTests'.
--
-- == Template syntax
--
-- A growth pin's @.ppl@ is a template over the knob its @.tst@ names
-- (@knob: N = 2, 4, 6@). Outside @{{ ... }}@ the text is copied verbatim.
--
-- * @{{N}}@, @{{N-1}}@, @{{i+2}}@ -- an integer: a literal or a bound name,
--   optionally plus or minus a literal.
-- * @{{for i in 1..N}}BODY{{end}}@ -- @BODY@ once per @i@ from the first bound
--   to the second, inclusive (nothing when the second is smaller), with @i@
--   bound inside it. @{{for i in 1..N sep ", "}}@ puts the quoted text between
--   copies. Loops nest.
--
-- == The growth verdict
--
-- Points are measured in knob order. Between consecutive measured points the
-- local log-log slope @log (f2/f1) / log (n2/n1)@ is the apparent polynomial
-- degree; for @f = n^k@ it is exactly @k@ at every pair, while an exponential
-- makes it climb with @n@. The climb stops at the first pair whose slope
-- exceeds the bound (plus a metric-dependent margin) -- the wall is still
-- there, so no point beyond it is paid for -- or at the first point that hits
-- the per-point cap, which counts as the same evidence: the knob values are
-- chosen so that a polynomial within the bound would stay far below the cap.
-- If every pair stays within the bound, the growth is (now) polynomial and the
-- pin reports "may be fixed". Successive ratios were the alternative; slopes
-- need no equal spacing and state their verdict in the bound's own unit.
module ScalingCheck
  ( Point(..)
  , Verdict(..)
  , expandTemplate
  , climb
  , localSlope
  , scalingCheckTests
  ) where

import Control.Monad (void)
import Data.Functor.Identity (runIdentity)
import Data.List (intercalate, isInfixOf)
import qualified Data.Map as Map
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Printf (printf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool, assertFailure)

-- ---------------------------------------------------------------------------
-- Templates
-- ---------------------------------------------------------------------------

type P = Parsec Void String

data IntExpr = IntExpr (Either Int String) Int

data Piece
  = PLit String
  | PInt IntExpr
  | PFor String IntExpr IntExpr String [Piece]

-- | Expand a template with the knob bound to the given value. A malformed
-- template or an unbound name is a 'Left' naming the problem.
expandTemplate :: String -> Int -> FilePath -> String -> Either String String
expandTemplate knob value fp src = do
  pieces <- either (Left . errorBundlePretty) Right (parse (many pPiece <* eof) fp src)
  render (Map.singleton knob value) pieces

render :: Map.Map String Int -> [Piece] -> Either String String
render env = fmap concat . mapM piece
  where
    piece (PLit s) = Right s
    piece (PInt e) = show <$> evalInt env e
    piece (PFor v lo hi sep body) = do
      a <- evalInt env lo
      b <- evalInt env hi
      copies <- mapM (\i -> render (Map.insert v i env) body) [a .. b]
      return (intercalate sep copies)

evalInt :: Map.Map String Int -> IntExpr -> Either String Int
evalInt env (IntExpr atom off) = case atom of
  Left n -> Right (n + off)
  Right v -> maybe (Left ("template names `" ++ v ++ "`, which is neither the knob nor a loop variable"))
                   (Right . (+ off)) (Map.lookup v env)

open_, close_ :: P ()
open_ = void (string "{{") >> hspace
close_ = hspace >> void (string "}}")

pPiece :: P Piece
pPiece = choice [try pFor, try pIntPiece, pLit]
  where
    pLit = PLit <$> some (notFollowedBy (string "{{") *> anySingle)
    pIntPiece = PInt <$> between open_ close_ pIntExpr
    pFor = do
      open_
      _ <- string "for" >> hspace1
      v <- pIdent <* hspace
      _ <- string "in" >> hspace1
      lo <- pIntExpr
      _ <- string ".." >> hspace
      hi <- pIntExpr
      -- pIntExpr has already eaten the space before a `sep`.
      sep <- option "" (try (hspace >> string "sep" >> hspace1 >> pQuoted))
      close_
      body <- many (notFollowedBy (try (open_ >> string "end" >> close_)) *> pPiece)
      open_ >> void (string "end") >> close_
      return (PFor v lo hi sep body)
    pQuoted = char '"' *> manyTill anySingle (char '"')

pIdent :: P String
pIdent = (:) <$> letterChar <*> many (alphaNumChar <|> char '_')

pIntExpr :: P IntExpr
pIntExpr = do
  atom <- (Left <$> L.decimal) <|> (Right <$> pIdent)
  hspace
  off <- option 0 $ do
    sign <- (id <$ char '+') <|> (negate <$ char '-')
    hspace
    n <- L.decimal
    hspace
    return (sign n)
  return (IntExpr atom off)

-- ---------------------------------------------------------------------------
-- The climb
-- ---------------------------------------------------------------------------

-- | One point of the family: the measured value, or the cap it ran into.
data Point = Measured Double | Capped String
  deriving (Show, Eq)

data Verdict
  = Exceeds String        -- ^ still grows faster than the bound; says where
  | WithinBound String    -- ^ every measured pair stayed within it; the table
  | Unmeasurable String   -- ^ the climb could not even start
  deriving (Show, Eq)

-- | A measured value: whole numbers (bytes, characters) as integers, a
-- wall time to three decimals.
showValue :: Double -> String
showValue f
  | f >= 100 = show (round f :: Integer)
  | otherwise = printf "%.3f" f

-- | The apparent polynomial degree between two measured points.
localSlope :: (Int, Double) -> (Int, Double) -> Double
localSlope (n1, f1) (n2, f2) =
  log (max tiny f2 / max tiny f1) / log (fromIntegral n2 / fromIntegral n1)
  where tiny = 1e-9

-- | Climb the knob values in order, measuring each with the given action, and
-- stop at the first evidence that the growth exceeds @bound@ (a slope above
-- it, or a capped point). @bound@ already includes the metric's margin.
climb :: Monad m => Double -> [Int] -> (Int -> m Point) -> m Verdict
climb _ [] _ = return (Unmeasurable "no knob values")
climb bound (n0 : ns) measure = do
  p0 <- measure n0
  case p0 of
    Capped why -> return (Unmeasurable (printf "the first point (%d) already hit the cap (%s): \
                                               \lower the knob values" n0 why))
    Measured f0 -> go [(n0, f0)] (n0, f0) ns
  where
    go seen _ [] = return (WithinBound (table seen))
    go seen prev (n : rest) = do
      p <- measure n
      case p of
        Capped why -> return (Exceeds (printf "%s; point %d hit the cap (%s)" (table seen) n why))
        Measured f ->
          let s = localSlope prev (n, f)
              seen' = seen ++ [(n, f)]
          in if s > bound
               then return (Exceeds (printf "%s; slope %.2f between %d and %d exceeds %.2f"
                                            (table seen') s (fst prev) n bound))
               else go seen' (n, f) rest
    table pts = intercalate ", " [ show n ++ " -> " ++ showValue f | (n, f) <- pts ]
                ++ slopes pts
    slopes pts = case zipWith localSlope pts (drop 1 pts) of
      [] -> ""
      ss -> " (slopes " ++ intercalate ", " (map (printf "%.2f") ss) ++ ")"

-- ---------------------------------------------------------------------------
-- Unit tests
-- ---------------------------------------------------------------------------

scalingCheckTests :: TestTree
scalingCheckTests = testGroup "KnownIssuesScaling"
  [ testCase "template: knob, offsets and a separated loop" $
      assertEqual "expansion"
        (Right "data R = R f1::Int, f2::Int, f3::Int\nmain = R 1 2 3 -- 3/2")
        (expandTemplate "N" 3 "t"
           "data R = R {{for i in 1..N sep \", \"}}f{{i}}::Int{{end}}\nmain = R{{for i in 1..N}} {{i}}{{end}} -- {{N}}/{{N - 1}}")
  , testCase "template: nested loops, empty range, single braces untouched" $
      assertEqual "expansion"
        (Right "x.{a} [1:1][2:1,2] ")
        (expandTemplate "K" 2 "t"
           "x.{a} {{for i in 1..K}}[{{i}}:{{for j in 1..i sep \",\"}}{{j}}{{end}}]{{end}} {{for i in 3..K}}never{{end}}")
  , testCase "template: an unbound name is an error" $
      case expandTemplate "N" 3 "t" "{{M}}" of
        Left err -> assertBool err ("`M`" `isInfixOf` err)
        Right r -> assertFailure ("expected an error, got " ++ show r)
  , testCase "slope of a power law is its degree" $ do
      assertBool "cubic" (abs (localSlope (4, 64) (8, 512) - 3) < 1e-9)
      assertBool "linear" (abs (localSlope (3, 30) (9, 90) - 1) < 1e-9)
  , testCase "climb: an exponential exceeds degree 2 and stops early" $ do
      let measured = runIdentity (climb 2.25 [2, 4, 6, 8, 10, 12] (pure . Measured . (2 **) . fromIntegral))
      case measured of
        Exceeds msg -> assertBool ("stopped before 12: " ++ msg) (not ("12 ->" `isInfixOf` msg))
        v -> assertFailure (show v)
  , testCase "climb: a quadratic with an offset stays within degree 2" $
      case runIdentity (climb 2.25 [2, 4, 8, 16] (\n -> pure (Measured (500 + fromIntegral (n * n))))) of
        WithinBound _ -> return ()
        v -> assertFailure (show v)
  , testCase "climb: a cubic exceeds degree 2" $
      case runIdentity (climb 2.25 [2, 4, 8] (\n -> pure (Measured (fromIntegral (n ^ (3 :: Int)))))) of
        Exceeds _ -> return ()
        v -> assertFailure (show v)
  , testCase "climb: a capped later point is evidence; a capped first point is unmeasurable" $ do
      let cappedAt k n = pure (if n >= k then Capped "10 s" else Measured (fromIntegral n))
      case runIdentity (climb 2.25 [1, 2, 3] (cappedAt 3)) of
        Exceeds _ -> return ()
        v -> assertFailure (show v)
      case runIdentity (climb 2.25 [1, 2, 3] (cappedAt 1)) of
        Unmeasurable _ -> return ()
        v -> assertFailure (show v)
  ]
