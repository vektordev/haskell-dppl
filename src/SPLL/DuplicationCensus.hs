-- | The duplication census (docs-repo design @ir-duplication-census@): how many
-- copies of each large subtree an unoptimized IR body holds.
--
-- An exponential compile blowup shows up as duplication long before it shows
-- up as size: a construct copied b times per nesting level already appears
-- about b^2 times at depth 2. So the census counts copies in small programs
-- rather than measuring size in big ones. It is read on IR /before/ the
-- optimizer (an @-O0@ compile), because CSE succeeding is what hides these
-- bugs: the @-O2@ output looks fine while compile time and memory explode.
--
-- It is CSE's analysis without applying it, with two deliberate differences
-- from 'SPLL.IROptimizer's table of equal nodes:
--
-- * It ignores guards. CSE rightly refuses to merge copies under different
--   @if@ guards, and those are the copies that stay expensive after @-O2@.
-- * Subtrees are keyed up to renaming of the variables they bind themselves:
--   a name bound inside the subtree (by 'IRLetIn' or 'IRLambda') hashes as its
--   de Bruijn index, a free name hashes as itself. Two compiles of one
--   expression then share a key, though their fresh names differ, while two
--   different outer variables never merge. (Stripping the numeric id off
--   fresh names is not enough: it merges distinct cells of one convolution.)
--
-- The node hash otherwise is CSE's ('headHash', 'hashMix'); a subtree's key is
-- its (hash, node count).
module SPLL.DuplicationCensus
  ( Duplicate(..)
  , FunctionCensus(..)
  , defaultMinSize
  , duplicatesIn
  , censusEnv
  , maxCopies
  , worstDuplicate
  , freshNameTags
  , renderCensus
  ) where

import Data.Char (isDigit)
import Data.List (foldl', sortOn)
import Data.Ord (Down(..))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import SPLL.IntermediateRepresentation
import SPLL.IROptimizer (headHash, hashMix)
import PrettyPrint (pPrintIRExpr)

-- | The smallest subtree counted, in IR nodes. Smaller values count noise
-- (repeated @IsAny@ tests, projections); larger ones delay detection by a
-- nesting level.
defaultMinSize :: Int
defaultMinSize = 30

-- | One subtree that occurs more than once in a body.
data Duplicate = Duplicate
  { dupCount   :: Int     -- ^ occurrences in the body
  , dupSize    :: Int     -- ^ IR nodes in one occurrence
  , dupExample :: IRExpr  -- ^ the first occurrence met
  }

-- | The duplicates of one compiled function body.
data FunctionCensus = FunctionCensus
  { fcGroup      :: String       -- ^ the 'IRFunGroup' name (a per-mask variant is its own group)
  , fcVariant    :: String       -- ^ @gen@, @prob@, @integ@, @writeLogits@ or @normal@
  , fcDuplicates :: [Duplicate]  -- ^ most copies first, then largest
  }

-- | A subtree annotated with its census facts. 'nHash' is the subtree's own
-- key hash (its binders as de Bruijn indices, its free names verbatim).
data Node = Node
  { nExpr :: IRExpr
  , nKids :: [Node]
  , nSize :: !Int
  , nFree :: Set.Set Varname
  , nHash :: Int
  }

annotate :: IRExpr -> Node
annotate e = n
  where
    kids = map annotate (getIRSubExprs e)
    n = Node e kids (1 + sum (map nSize kids)) free (nodeHash Map.empty 0 n)
    free = case (e, kids) of
      (IRVar x, _)              -> Set.singleton x
      (IRLetIn x _ _, [a, b])   -> nFree a `Set.union` Set.delete x (nFree b)
      (IRLambda x _, [b])       -> Set.delete x (nFree b)
      _                         -> Set.unions (map nFree kids)

-- | The hash of a node with the binders of an enclosing subtree in scope:
-- @env@ maps each bound name to the depth of its binder, @depth@ counts the
-- binders entered so far. A child that reads none of @env@ hashes as it does
-- alone, so only the paths that reach an enclosing binder are rehashed.
nodeHash :: Map.Map Varname Int -> Int -> Node -> Int
nodeHash env depth n = case (nExpr n, nKids n) of
  (IRVar x, _) -> case Map.lookup x env of
    Just lvl -> hashMix 41 (depth - lvl)
    Nothing  -> headHash (IRVar x)
  (IRLetIn x _ _, [a, b]) -> foldl' hashMix 42 [child env depth a, child (Map.insert x depth env) (depth + 1) b]
  (IRLambda x _, [b])     -> hashMix 43 (child (Map.insert x depth env) (depth + 1) b)
  (e, kids)               -> foldl' hashMix (headHash e) (map (child env depth) kids)
  where
    child env' depth' c
      | readsEnv env' c = nodeHash env' depth' c
      | otherwise    = nHash c
    readsEnv env' c
      | Map.null env' = False
      | Set.size (nFree c) <= Map.size env' = any (`Map.member` env') (Set.toList (nFree c))
      | otherwise = any (`Set.member` nFree c) (Map.keys env')

-- | Every subtree of at least @minSize@ nodes that occurs more than once in
-- the expression, most copies first, then largest. Occurrences inside another
-- occurrence count: a subtree copied twice inside a block that is itself
-- copied twice has four copies.
duplicatesIn :: Int -> IRExpr -> [Duplicate]
duplicatesIn minSize e0 =
  sortOn (\d -> (Down (dupCount d), Down (dupSize d)))
    [ Duplicate c sz ex | ((_, sz), (c, ex)) <- Map.toList table, c > 1 ]
  where
    table = go (annotate e0) Map.empty
    go n m =
      let m' = foldl' (flip go) m (nKids n)
      in if nSize n >= minSize
           then Map.insertWith (\_ (c, ex) -> (c + 1, ex)) (nHash n, nSize n) (1 :: Int, nExpr n) m'
           else m'

-- | The census of every function body of an environment.
censusEnv :: Int -> IREnv -> [FunctionCensus]
censusEnv minSize (IREnv groups _ _) =
  [ FunctionCensus (groupName g) label (duplicatesIn minSize body)
  | g <- groups
  , (label, field) <- [ ("gen", genFun), ("prob", probFun), ("integ", integFun)
                      , ("writeLogits", writeLogitsFun), ("normal", normalFun) ]
  , Just (body, _) <- [field g] ]

-- | M: the copy count of the most-copied counted subtree; 1 when nothing is
-- duplicated.
maxCopies :: FunctionCensus -> Int
maxCopies = maybe 1 dupCount . worstDuplicate

worstDuplicate :: FunctionCensus -> Maybe Duplicate
worstDuplicate fc = case fcDuplicates fc of
  (d : _) -> Just d
  []      -> Nothing

-- | The tags of the compiler's fresh names in a subtree (@l_17_open_body@ has
-- the tag @open_body@), most frequent first. They usually name the site that
-- built the subtree.
freshNameTags :: IRExpr -> [String]
freshNameTags e = map fst (sortOn (Down . snd) (Map.toList counts))
  where
    counts = Map.fromListWith (+) [ (t, 1 :: Int) | Just t <- map tagOf (names e) ]
    names x = case x of
      IRVar n        -> n : []
      IRLetIn n a b  -> n : names a ++ names b
      IRLambda n a   -> n : names a
      _              -> concatMap names (getIRSubExprs x)
    -- A renamed fresh name (@l_2_l_0_a@) keeps its original's tag.
    tagOf n = case n of
      'l' : '_' : rest | ((_ : _), '_' : t) <- span isDigit rest, not (null t) -> Just (maybe t id (tagOf t))
      _ -> Nothing

-- | The @--duplicationCensus@ report: per function body with a duplicate,
-- highest M first, its M and its @top@ most-copied subtrees, with their tags
-- and their text cut to a few lines; the bodies without one on a last line.
renderCensus :: Int -> Int -> [FunctionCensus] -> String
renderCensus minSize top fcs = unlines $
  ("=== Duplication census (unoptimized IR, subtrees of >= " ++ show minSize ++ " nodes) ===")
  : concatMap one (sortOn (Down . maxCopies) dupd)
  ++ [ "  no duplicate in: " ++ unwords [ fcGroup fc ++ "." ++ fcVariant fc | fc <- clean ] | not (null clean) ]
  where
    (dupd, clean) = (filter (not . null . fcDuplicates) fcs, filter (null . fcDuplicates) fcs)
    one fc =
      ("  " ++ fcGroup fc ++ " [" ++ fcVariant fc ++ "]: M = " ++ show (maxCopies fc)
         ++ ", " ++ show (length (fcDuplicates fc)) ++ " duplicated subtrees")
      : concatMap dup (take top (fcDuplicates fc))
    dup d =
      [ "    " ++ show (dupCount d) ++ " copies of " ++ show (dupSize d) ++ " nodes, tags: "
          ++ unwords (take 6 (freshNameTags (dupExample d))) ]
      ++ map ("      | " ++) (excerpt (pPrintIRExpr (dupExample d) 0))
    excerpt s = let ls = filter (not . all (== ' ')) (lines s)
                in map (cut 120) (take 8 ls) ++ [ "..." | length ls > 8 ]
    cut k l = if length l > k then take k l ++ "..." else l
