{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module SPLL.CodeGenPyTorch (
  generateFunctions,
  generateFunctionsWith,
  MemoPlan(..),
  memoPlan,
  memoDecorate,
  pyVal,
  envToLUT,
  normalRefName,
  replaceCalls,
  pyMangle,
  groupClassName,
  pyDouble,
  pyAttrBase,
  pythonKeywords,
  irFreeVars
) where

import SPLL.IntermediateRepresentation
import SPLL.ReservedNames (pythonKeywords, pythonReservedIdentifiers, pythonNeedsEscape, componentNormalName)
import SPLL.IRSelectPass (desugarSelectEnv)
import SPLL.PythonNesting (tooDeepForPython, spillDeep, adtCallees, renameFree, pythonMaxIndent, blockIndent, bindIterable, hasAssignmentExpr)
import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..), shapeRank, shapeNumel)
import SPLL.Typing.AlgebraicDataTypes (anyCtorTestMessage, accessorMismatchMessage, fieldAccessorOwners)
import Data.List (intercalate, intersperse, isPrefixOf, dropWhileEnd, nub)
import Data.Char (toUpper, isDigit)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State (StateT (runStateT), MonadState (get, put), MonadTrans (lift), gets, modify)
import Utils (Supply, demandUniqueNumber, evalSupply)

--TODO: On the topic of memoization: Ideally we would want to optimize away redundant calls within a loop.
-- e.g. in MNist-Addition

--TODO: Recursive calls should be phrased as self.forward rather than (modulename).forward.

-- Expected format format of ThetaTrees:
--    ThetaTree = ([Double], [ThetaTree])

-- | The state threaded through one class's code generation.
data CodegenState = CodegenState
  { stGlobalMultis :: [(GenericMultiValue IRExpr, String)]
    -- ^ class-level constants, one per distinct 'MultiValue' an
    -- 'IRIsPossible' reads
  , stCallables :: [String]
    -- ^ names whose bare reference is a call (nullary functions and
    -- constructors)
  , stAdtCalls :: [String]
    -- ^ the ADT constructors, tests and accessors, which a spill may move
    -- ('SPLL.PythonNesting.adtCallees')
  , stHoistDeeperThan :: Maybe Int
    -- ^ when set, a statement block nested deeper than this is hoisted into
    -- a local function ('hoistDeepBlock'). Set only while regenerating a
    -- method whose plain rendering is indented deeper than Python accepts.
  , stHoisted :: [[String]]
    -- ^ the current method's hoisted functions, most recent first
  }

type GlobalStorage = StateT CodegenState
type VariableSupply = Supply
type GlobalVariableSupply a = GlobalStorage VariableSupply a

addOrGetFromGlobalStorage :: GenericMultiValue IRExpr -> GlobalVariableSupply String
addOrGetFromGlobalStorage mv = do
  st <- get
  case lookup mv (stGlobalMultis st) of
    Nothing -> do
      varID <- lift demandUniqueNumber
      let varName = "_globalMulti" ++ show varID
      put st { stGlobalMultis = (mv, varName) : stGlobalMultis st }
      return varName
    Just var -> return var

indentOnce :: [String] -> [String]
indentOnce = map ("    " ++)

pyOps :: Operand -> String
pyOps OpPlus = "+"
pyOps OpMult = "*"
pyOps OpGreaterThan = ">"
pyOps OpLessThan = "<"
pyOps OpDiv = "/"
pyOps OpIntDiv = "//"
pyOps OpMod = "%"
pyOps OpSub = "-"
pyOps OpOr = "or"
pyOps OpAnd = "and"
pyOps OpEq = "=="
pyOps x = error $ "Operator has no infix representation: " ++ show x

pyDistName :: Distribution -> String
pyDistName IRNormal = "normal"
pyDistName IRUniform = "uniform"

pyUnaryOps :: UnaryOperand -> String
pyUnaryOps OpNeg = "-"
pyUnaryOps OpExp = "safe_exp"
pyUnaryOps OpAbs = "abs"
pyUnaryOps OpNot = "not"
pyUnaryOps OpLog = "safe_log"
pyUnaryOps OpSign = "sign"
pyUnaryOps OpIsAny = "isAny"

-- | A 'Double' as a Python float literal.
--
-- Haskell's 'show' renders the three non-finite doubles as @Infinity@,
-- @-Infinity@ and @NaN@ -- none of which is a Python name. Emitting them
-- produced code that raised @NameError@ at run time instead of failing the
-- compile, and log space reaches them constantly: its zero is @-1/0@
-- ('SPLL.Semiring.negInfIR'), so every impossible arm of a @--logSpace@
-- program carried an undefined name. @float('inf')@ needs no import, unlike
-- @math.inf@.
pyDouble :: Double -> String
pyDouble f
  | isNaN f      = "float('nan')"
  | isInfinite f = if f > 0 then "float('inf')" else "float('-inf')"
  | otherwise    = show f

pyVal :: IRValue -> String
pyVal (VList EmptyList) = "EmptyInferenceList()"
pyVal (VList AnyList) = "AnyInferenceList()"
-- The cons spine is rendered as a difference string: @rest ++ ")"@ at every
-- cell re-copied the whole tail, quadratic in a long constant list such as a
-- V-value enumeration domain (task neural-int-read-compile-quadratic-in-domain).
pyVal (VList l@(ListCont _ _)) = cells l ""
  where
    cells (ListCont x xs) = showString "ConsInferenceList(" . showString (pyVal x) . showString ", " . cells xs . showString ")"
    cells rest = showString (pyVal (VList rest))
pyVal (VInt i) = show i
pyVal (VFloat f) = pyDouble f
pyVal (VBool f) = if f then "True" else "False"
pyVal (VTuple a b) = "T(" ++ pyVal a ++ ", " ++ pyVal b ++ ")"
pyVal (VEither (Left a)) = "Left(" ++ pyVal a ++ ")"
pyVal (VEither (Right a)) = "Right(" ++ pyVal a ++ ")"
pyVal VUnit = "None"
pyVal (VThetaTree tt) = pyValTree tt
  where pyValTree (ThetaTree val trees) = "([" ++ intercalate ", " (map pyDouble val) ++ "], [" ++ intercalate ", " (map pyValTree trees) ++ "])"
pyVal (VADT cName params) = pyCtorRef cName ++ "(" ++ intercalate ", " (map pyVal params) ++ ")"
-- A rank-1 tensor is a Python list, as 'BTensor' renders one. Higher rank has
-- no runtime representation yet (see the 'BTensor' case of 'generateExpression').
pyVal (VTensor sh xs)
  | shapeRank sh == 1 = "[" ++ intercalate ", " (map pyVal xs) ++ "]"
  | otherwise = error (rankUnsupported "a tensor value" (shapeRank sh))
pyVal (VAny) = "'ANY'"
pyVal (VError e) = "throw(\"" ++ e ++ "\")"
-- 'VAnyExcept' has no runtime representation in the Python runtime library
-- (unlike VAny/AnyList above, which both render as real sentinels), so there
-- is no string to emit here -- this is a backstop only. The intended refusal
-- point is 'SPLL.IntermediateRepresentation.anyExceptCodegenRefusal', called
-- from 'Main.codeGenToLang' before 'generateFunctions' is ever reached; a
-- direct caller of 'generateFunctions' that skips that check lands here
-- instead of the generic "unknown pyVal" panic below (task
-- vanyexcept-unrenderable-in-text-backends).
pyVal v@(VAnyExcept _) = error (unlines
  [ "pyVal: unconsumed VAnyExcept placeholder reached Python codegen: " ++ show v
  , "This should have been refused earlier by"
  , "SPLL.IntermediateRepresentation.anyExceptCodegenRefusal; a caller reached"
  , "generateFunctions without that guard."
  , "(task vanyexcept-unrenderable-in-text-backends)" ])
pyVal x = error ("unknown pyVal for " ++ show x)

pyMultiVal :: GenericMultiValue IRExpr -> String
pyMultiVal MultiContinuous = "(\"C\", None)"
pyMultiVal (MultiDiscretes vals) = "(\"D\", [" ++ intercalate ", " (map (pyVal . valueToIR) vals) ++ "])"
pyMultiVal (MultiTuple l r) = "(\"T\", (" ++ pyMultiVal l ++ ", " ++ pyMultiVal r ++ "))"
pyMultiVal (MultiEither l r) = "(\"E\", (" ++ pyMultiVal l ++ ", " ++ pyMultiVal r ++ "))"
pyMultiVal (MultiADT constrs) = "(\"A\", [" ++ intercalate ", " (map (\(cName, fields) -> 
  "(" ++ pyCtorRef cName ++ ", [" ++ intercalate ", " (map pyMultiVal fields) ++ "])"
  ) constrs) ++ "])"
-- MultiAuto and MultiTypeRef are resolved by AutoNeural before codegen: the
-- first by auto-derivation from the RType, the second by unrolling the
-- depth-bounded recursion. Reaching codegen means that pass was skipped.
pyMultiVal x = error ("unresolved MultiValue in codegen: " ++ show x)

-- 'pythonKeywords' (the words 'pyMangle' escapes) lives in
-- 'SPLL.ReservedNames', the registry of every name the pipeline claims.

-- | Make a name safe to emit as a Python identifier, by appending the
-- conventional trailing underscore. The escaped set is
-- 'SPLL.ReservedNames.pythonReservedIdentifiers': the keywords, @self@, and
-- every name the module already has in scope -- the runtime's classes, its
-- other star-imported values (@randn@, @exp@, @pi@, ...) and Python's builtins,
-- any of which a user definition or binder of the same spelling would shadow.
-- A constructor is escaped also when the predicate it derives is one of these
-- ('SPLL.ReservedNames.pythonNeedsEscape': @Any@ derives the runtime's
-- @isAny@), so its predicate is spelled from the escaped name (@isAny_@).
-- Applied to ADT names by
-- 'renameADTIdentifiers' and to every other user name (function groups,
-- parameters, binders) by 'mangleUserIdentifiers'.
--
-- The rule fires not only on a keyword but on a keyword followed by any run of
-- underscores, and that is what makes it injective. Mangling only exact
-- keywords would map the distinct source names @None@ and @None_@ onto the
-- same @None_@ -- emitting two @class None_:@ definitions, the second silently
-- shadowing the first, so values of one constructor would answer the other's
-- predicate. Escaping the whole family instead shifts @kw@, @kw_@, @kw__@, ...
-- each one underscore along; the family maps into itself injectively, every
-- other name maps to itself, and the two images are disjoint because anything
-- of the form @kw_@+ is by definition in the family.
--
-- Injectivity holds within this family, not across the whole ADT namespace: a
-- field named @isNone_@ in a program that also declares a constructor @None@
-- still collides with that constructor's derived predicate. Nothing here can
-- see that -- mangling is deliberately a pure function of one name, which is
-- what lets 'pyVal' mangle a query point that never passed through
-- 'renameADTIdentifiers'. 'adtIdentifierRenaming' carries the cross-family
-- check instead, where the whole declaration set is in scope.
pyMangle :: String -> String
pyMangle name
  | pythonNeedsEscape (dropWhileEnd (== '_') name) = name ++ "_"
  | otherwise                                     = name

-- | 'pyMangle' for a constructor reference in a rendered value, which the test
-- harness may have qualified with a module path. Only the final segment is an
-- identifier this backend owns; a qualifier is the caller's and is passed
-- through untouched.
pyCtorRef :: String -> String
pyCtorRef name = case break (== '.') (reverse name) of
  (revLast, '.':revQual) -> reverse revQual ++ "." ++ pyMangle (reverse revLast)
  _                      -> pyMangle name

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs
onHead _ [] = []

generateFunctions :: Bool -> IREnv -> [String]
generateFunctions = generateFunctionsWith False

-- | 'generateFunctions', with the recursion memo ('memoPlan') switched on by
-- the first argument (CLI @--memoRecursion@). Off, the output is exactly
-- 'generateFunctions''.
generateFunctionsWith :: Bool -> Bool -> IREnv -> [String]
--contrary to the julia backend, we want to aggregate gen and prob into one classes. Ugly implementation, but it'll do for now.
generateFunctionsWith memo genBoil env0 =
    -- Scalar backend: lower any IRSelect (from batched mode's select pass) back
    -- to IRIf up front, so the rest of codegen never sees it (pytorch-tensorizer
    -- M1, strategy B).
    let env@(IREnv funcs adtsEnv consts) = mangleUserIdentifiers pyMangle (renameADTIdentifiers pyMangle (desugarSelectEnv (retireUnrenderableVariants "Python" env0)))
        clsName = groupClassName env
        lut = envToLUT env ++ stdLib
        -- A nullary function is referenced in the IR by a bare 'IRVar' (there is
        -- no nullary 'IRApply'), which the interpreter reads as its value; here
        -- the reference has to become a call. That holds for a nullary normal
        -- function as much as a generator: writeLogits of @main = Normal * 3.0@
        -- reads @main_normal@'s (mu, sigma) and indexed the method object.
        decorators = if memo then memoDecorators (memoPlan env) else const []
        callableNames = [ fromMaybe (n ++ "_gen") (lookup (n ++ "_gen") lut)
                        | IRFunGroup{groupName=n, genFun=Just (e, _)} <- funcs
                        , null (fst (unwrapLambdas e)) ]
                        ++ [ fromMaybe ref (lookup ref lut)
                           | IRFunGroup{groupName=n, normalFun=Just (e, _)} <- funcs
                           , null (fst (unwrapLambdas e))
                           , let ref = normalRefName n ]
                        -- nullary ADT constructors must be emitted as instantiations,
                        -- otherwise the bare class never compares equal to enumerated instances
                        ++ [ pyMangle cName | decl <- adtsEnv, (cName, fields) <- constructors decl, null fields ]
    in if genBoil then
      ["from pythonLib import *",
      "import functools",
      "import math",
      "from torch.nn import Module", ""] ++
      generateADTClasses adtsEnv ++
      map (\(name, val) -> name ++ " = " ++ pyVal val) consts ++
      (if null consts then [] else [""]) ++
      concatMap (generateClass clsName lut callableNames (adtCallees pyMangle adtsEnv) decorators) funcs ++
      ["", "# Example Initialization"] ++
      generateInitializations env
    else
      map (\(name, val) -> name ++ " = " ++ pyVal val) consts ++
      concatMap (generateClass clsName lut callableNames (adtCallees pyMangle adtsEnv) decorators) funcs


stdLib :: [(String, String)]
stdLib = [("in", "contains")]

envToLUT :: IREnv -> [(String, String)]
envToLUT (IREnv funcs _ _) = concatMap (\IRFunGroup {groupName=n} -> [(n ++ "_gen", n ++ ".generate"), (n ++ "_prob", n ++ ".forward"), (n ++ "_integ", n ++ ".integrate"), (normalRefName n, n ++ ".normal_params")]) funcs

-- | The name the IR references a group's normal function by: @f_normal@, or the
-- bare component name for a tuple component's own group
-- ('SPLL.ReservedNames.componentNormalName'). The component group is emitted as
-- an instance @_component_f_normal_fst@ whose method is @normal_params@, so
-- without this a reference to @f_normal_fst@ named nothing.
normalRefName :: String -> String
normalRefName n = fromMaybe (n ++ "_normal") (componentNormalName n)

replaceCalls :: [(String, String)] -> IRExpr -> IRExpr
replaceCalls lut (IRVar name) = IRVar (fromMaybe name $ lookup name lut)
replaceCalls _ other = other

generateInitializations :: IREnv -> [String]
generateInitializations env@(IREnv funcs _ _) = map (\IRFunGroup {groupName=n} -> n ++ " = " ++ groupClassName env n ++ "()") funcs

-- | The Python class a function group is emitted as: its (already mangled)
-- name capitalised -- @main@ is @class Main@ -- unless that spelling is already
-- taken, in which case underscores are appended until it is free.
--
-- Capitalising is what makes this necessary: it can land a group's class on a
-- name the module already defines, and a Python class definition silently
-- replaces the earlier one. @none@ capitalises to the keyword @None@ (a
-- @SyntaxError@), @t@ to the runtime's tuple class @T@ (every tuple then fails
-- to construct), and a definition @foo@ beside a constructor @Foo@ replaced the
-- constructor's class, so @foo@'s own @Foo()@ built an instance of its module
-- class instead -- a silently wrong value. Taken: every name 'pyMangle'
-- escapes, every name the ADT declarations emit, and the classes assigned to
-- earlier groups. The class name is internal (callers use the instance, named
-- after the group), so renaming it changes no interface; a program with no
-- clash is emitted exactly as before.
groupClassName :: IREnv -> String -> String
groupClassName (IREnv funcs adtDecls _) n = fromMaybe (onHead toUpper n) (lookup n table)
  where
    table = reverse (snd (foldl assign (taken0, []) (map groupName funcs)))
    assign (taken, acc) g =
      let c = until (`notElem` taken) (++ "_") (onHead toUpper g) in (c : taken, (g, c) : acc)
    taken0 = pythonReservedIdentifiers
          ++ concat [ pyMangle c : ("is" ++ pyMangle c) : [ pyMangle f | (f, _) <- fields ]
                    | d <- adtDecls, (c, fields) <- constructors d ]

generateADTClasses :: [ADTDecl] -> [String]
generateADTClasses decls =
  concatMap generateADTClass (concatMap constructors decls)
  ++ concatMap (uncurry generateADTAccessor) (fieldAccessorOwners decls)

-- Every identifier printed here goes through 'pyMangle'; the declaration itself
-- keeps the names the user wrote (see 'renameADTIdentifiers'). The one place
-- the *source* name is used instead is 'anyCtorTestMessage', which must read
-- identically across all three backends and the interpreter.
generateADTClass :: ADTConstructorDecl -> [String]
generateADTClass (name, fields) =
  -- Class declaration
  ["class " ++ cls ++ ":"]++
  indentOnce (
    -- Constructor
    ("def __init__(self, " ++ intercalate ", " fieldNames ++ "):") :
    case fieldNames of
      [] -> indentOnce ["pass"]
      fieldNamesList -> indentOnce (
        map (\f -> "self." ++f ++ " = " ++ f) fieldNamesList ++
        ["self._fields = [" ++ intercalate ", " fieldNamesList ++ "]"])
  ) ++ [""] ++
  indentOnce (
    "def __eq__(self, other):":
      indentOnce (
        ("if not isinstance(other, " ++ cls ++ "): return False"):
        map (\f -> "if not eq(self." ++ f ++ ", other." ++ f ++ "): return False") fieldNames ++
        ["return True"]
      )
  ) ++ [""] ++
  -- Is function. The ANY refusal keeps this in step with the interpreter's
  -- 'isImpl'; `isinstance` would answer False for a hole and silently drop the
  -- branch. See 'anyCtorTestMessage'.
  ["def is" ++ cls ++ "(x):"] ++
  indentOnce ["if isAny(x): throw(" ++ show (anyCtorTestMessage name) ++ ")",
              "return isinstance(x, " ++ cls ++ ")"]
  where cls = pyMangle name
        fieldNames = map pyMangle (map fst fields)

-- | One field accessor, guarded on the constructor that owns the field.
--
-- Without the guard this was @return x.color@, so reading a field off a sibling
-- constructor raised @AttributeError: \'Nil\' object has no attribute
-- \'color\'@ -- a target-language accident with no SPLL-level content, and one
-- the type checker cannot rule out ('accessorMismatchMessage' says why). The
-- accessor is still partial; it now says so in the compiler's own words. The
-- @Got:@ suffix keeps the one thing the @AttributeError@ did tell you.
--
-- Emitted once per field *name*, not once per constructor: see
-- 'fieldAccessorOwners'.
generateADTAccessor :: String -> String -> [String]
generateADTAccessor fieldName ctorName =
  ("def " ++ pyMangle fieldName ++ "(x):") :
  indentOnce [ "if not isinstance(x, " ++ pyMangle ctorName ++ "): throw("
                 ++ show (accessorMismatchMessage fieldName ctorName)
                 ++ " + \" Got: \" + type(x).__name__)"
             , "return x." ++ pyMangle fieldName ]

generateClass :: (String -> String) -> [(String, String)] -> [String] -> [String] -> (String -> [String]) -> IRFunGroup -> [String]
generateClass clsName lut callableNames adtCalls decorators (IRFunGroup name gen prob integ writeLogits normal doc _ _ _) = let
  funcStringFromMaybe fname func = case func of
    Just a -> generateFunction True (fname, replaceCallsDecl a)
    Nothing -> return []
  ((i, p, g, e, n), CodegenState { stGlobalMultis = globalVars }) = evalSupply $ runStateT (do
    i' <- memoDecorate (decorators (name ++ "_integ")) <$> funcStringFromMaybe "integrate" integ
    p' <- memoDecorate (decorators (name ++ "_prob")) <$> funcStringFromMaybe "forward" prob
    g' <- funcStringFromMaybe "generate" gen
    e' <- funcStringFromMaybe "writeLogits" writeLogits
    n' <- funcStringFromMaybe "normal_params" normal
    return (i', p', g', e', n')) (CodegenState [] callableNames adtCalls Nothing [])
  commentLines = map ("# " ++) (lines doc)
  initLine = "class " ++ clsName name ++ "(Module):"
  globalVarDecls = map (\(mv, varName)-> varName ++ " = " ++ pyMultiVal mv) globalVars
  -- A group left with no methods (e.g. -G -I -P on a main that only calls a
  -- neural declaration, which has no writeLogits/normal_params either) would
  -- otherwise print a class header over blank lines, an IndentationError. A
  -- `pass` body keeps the module importable and the instance line valid, as
  -- in the batched backend (task all-functions-flags-empty-main-class).
  funcs
    | all null [i, p, g, e, n] && null globalVars = ["pass"]
    | otherwise = i ++ [""] ++ p ++ [""] ++ g ++ [""] ++ e ++ [""] ++ n
  replaceCallsDecl (expr, d) = (irMap (replaceCalls lut) expr, d)
  in commentLines ++ initLine:indentOnce globalVarDecls ++ indentOnce funcs

-- ---------------------------------------------------------------------------
-- The recursion memo (task recursive-prob-calls-not-shared-across-branches)
-- ---------------------------------------------------------------------------
--
-- A recursive probability function called with the same arguments from
-- several branches recomputes the whole subtree each time: an HMM's
-- likelihood calls @gen.forward(sample[1:], s)@ for both hidden states from
-- both hidden-state arms, 2^n calls where the forward algorithm needs 2n.
-- Under @--memoRecursion@ the probability and integrate methods on a recursive
-- call cycle are wrapped in the runtime's @nest_memo@, which answers a repeated
-- call from a table keyed on the method and its argument values. The table
-- lives for one top-level query: the first emitted method call opens it and
-- drops it when it returns, so it never serves values computed under other
-- weights. Methods off the cycle that reach it are wrapped in
-- @nest_memo_scope@, which only opens the table, so that the calls one query
-- makes into the cycle from several places share it. The keying rules (and
-- why identity keys are safe there) are in the runtimes, next to @nest_memo@.

-- | Which emitted methods the memo wraps, by raw IR name (@f_prob@,
-- @f_integ@): those on a recursive call cycle, and those off it that reach
-- one. Both are empty for a program without recursion.
data MemoPlan = MemoPlan { memoMembers :: Set.Set String, memoScopes :: Set.Set String }
  deriving (Eq, Show)

memoPlan :: IREnv -> MemoPlan
memoPlan (IREnv funcs _ _) = MemoPlan members scopes
  where
    methods = Map.fromList $
         [ (n ++ "_prob", e)  | IRFunGroup{groupName=n, probFun=Just (e, _)} <- funcs ]
      ++ [ (n ++ "_integ", e) | IRFunGroup{groupName=n, integFun=Just (e, _)} <- funcs ]
    callees = Map.map (Set.filter (`Map.member` methods) . varNames) methods
    varNames e = Set.fromList [ v | IRVar v <- universeIR e ]
    universeIR e = e : concatMap universeIR (getIRSubExprs e)
    reach m = go Set.empty (Set.toList (Map.findWithDefault Set.empty m callees))
      where go seen [] = seen
            go seen (x:xs)
              | x `Set.member` seen = go seen xs
              | otherwise = go (Set.insert x seen) (Set.toList (Map.findWithDefault Set.empty x callees) ++ xs)
    reaches = Map.mapWithKey (\m _ -> reach m) methods
    members = Map.keysSet (Map.filterWithKey Set.member reaches)
    scopes
      | Set.null members = Set.empty
      | otherwise = Map.keysSet (Map.filterWithKey (\m r -> m `Set.notMember` members
                                                         && not (Set.disjoint r members)) reaches)

-- | The decorator lines for one raw method name under a plan.
memoDecorators :: MemoPlan -> String -> [String]
memoDecorators (MemoPlan members scopes) raw
  | raw `Set.member` members = ["@nest_memo"]
  | raw `Set.member` scopes  = ["@nest_memo_scope"]
  | otherwise                = []

-- | Put decorator lines on an emitted method: right above its @def@ line,
-- after its comment lines.
memoDecorate :: [String] -> [String] -> [String]
memoDecorate [] ls = ls
memoDecorate decos ls = case break ("def " `isPrefixOf`) ls of
  (before, defLine : rest) -> before ++ decos ++ defLine : rest
  _                        -> ls

generateFunction :: Bool -> (String, IRFunDecl) -> GlobalVariableSupply [String]
generateFunction classFunction (name, (expr, doc)) = do
  let (args, reducedExpr) = unwrapLambdas expr
  let args' = if classFunction then "self":args else args
  let l1 = "def " ++ name ++ "(" ++ intercalate ", " args' ++ "):"
  block <- if classFunction then generateMethodBody reducedExpr
                             else generateStatementBlock reducedExpr
  let docLines = map ("# " ++) (lines doc)
  return $ docLines ++ [l1] ++ indentOnce block

-- ---------------------------------------------------------------------------
-- Hoisting deeply nested blocks (task
-- python-nested-conditionals-exceed-indentation-limit)
-- ---------------------------------------------------------------------------
--
-- CPython refuses a line indented 100 levels deep (@MAXINDENT@, "too many
-- levels of indentation"), a constant like the bracket limit 'liftedLine'
-- spills around. Statement emission indents one level per conditional whose
-- arms hold another conditional, and one per spilled loop, so ~97 nested
-- @if@s in a method body made the module unimportable.
--
-- The fix mirrors the bracket spill: a method is rendered as before and
-- measured; only one whose deepest line passes 'pythonMaxIndent' is
-- regenerated with hoisting switched on. Every module that loaded before is
-- byte-identical. While regenerating, a statement block (an @if@ arm or a
-- spilled loop's body) nested deeper than 'hoistIndentThreshold' becomes a
-- local function defined at the top of the method body, and the block itself
-- becomes one call (@name = _hN(a, b)@, or @return _hN(a, b)@ for a block that
-- returns). The function is called exactly where the block ran, so guards and
-- evaluation order are unchanged.
--
-- The functions are flat -- all at the method's top level, never nested in
-- one another -- since a @def@ body is an indentation level of its own and
-- nesting them would give back one level per hoist. Being flat, a hoisted
-- block cannot see a variable bound in the enclosing block it was cut from
-- (which may itself be a hoisted function's local), so it is closure
-- converted: every free IR variable of the block is a parameter, passed at
-- the call. Only the method's own parameters and @self@ would be reachable as
-- closures anyway; passing them is harmless. Globals (dotted method
-- references, 'stCallables') are left to resolve as before.

-- | The indentation of a class method's body: class, then @def@.
methodBodyIndent :: Int
methodBodyIndent = 2

-- | How deep (in indentation levels) a block may be before 'hoistDeepBlock'
-- cuts it out while hoisting is on. Well under 'pythonMaxIndent', so a
-- hoisted function's body plus whatever its call site is nested in still fits;
-- high enough that only a few levels in a hundred cost a call.
hoistIndentThreshold :: Int
hoistIndentThreshold = 32

-- | A class method's body: as 'generateStatementBlock' renders it, unless
-- that is too deeply indented for Python, in which case it is regenerated with
-- deep blocks hoisted into local functions defined at its top.
generateMethodBody :: IRExpr -> GlobalVariableSupply [String]
generateMethodBody e = do
  st0 <- get
  block <- generateStatementBlock e
  if methodBodyIndent + blockIndent block <= pythonMaxIndent
    then return block
    else do
      put st0 { stHoistDeeperThan = Just hoistIndentThreshold, stHoisted = [] }
      block' <- generateStatementBlock e
      hoisted <- gets stHoisted
      modify (\st -> st { stHoistDeeperThan = Nothing, stHoisted = [] })
      return (concat (reverse hoisted) ++ block')

-- | Hoist one emitted block, the rendering of the IR @src@, into a local
-- function if hoisting is on and the block is deeper than allowed. @target@ is
-- the variable the block assigns, or 'Nothing' for a block that returns.
hoistDeepBlock :: IRExpr -> Maybe String -> [String] -> GlobalVariableSupply [String]
hoistDeepBlock src target stmts = do
  st <- get
  case stHoistDeeperThan st of
    Just limit | blockIndent stmts > limit -> do
      n <- lift demandUniqueNumber
      let fn = "_h" ++ show n
          params = [ v | v <- irFreeVars src, '.' `notElem` v, v `notElem` stCallables st ]
          call = fn ++ "(" ++ intercalate ", " params ++ ")"
          body = stmts ++ maybe [] (\t -> ["return " ++ t]) target
          def = ("def " ++ call ++ ":") : indentOnce body
      put st { stHoisted = def : stHoisted st }
      return [maybe ("return " ++ call) (\t -> t ++ " = " ++ call) target]
    _ -> return stmts

-- | The free variables of an IR expression, in order of first occurrence.
irFreeVars :: IRExpr -> [String]
irFreeVars = nub . go []
  where
    go bound e = case e of
      IRVar v -> [v | v `notElem` bound]
      IRLetIn n v b -> go bound v ++ go (n : bound) b
      IRLambda n b -> go (n : bound) b
      _ -> concatMap (go bound) (getIRSubExprs e)

unwrapLambdas :: IRExpr -> ([String], IRExpr)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

-- | True when the block is exactly one if-elif-else construct with nothing after it.
-- After the else: body ends, no further top-level lines may appear.
isSingleIfBlock :: [String] -> Bool
isSingleIfBlock (l:ls) | "if " `isPrefixOf` l = afterIf ls
isSingleIfBlock _ = False

-- Scanning lines that may be elif/else or indented body after the opening if.
afterIf :: [String] -> Bool
afterIf [] = True
afterIf (l:ls)
  | "    " `isPrefixOf` l  = afterIf ls
  | "elif " `isPrefixOf` l = afterIf ls
  | l == "else:"           = afterElse ls
  | otherwise              = False   -- second if, bare assignment, etc.

-- Scanning lines inside an else: body; nothing may follow outside it.
afterElse :: [String] -> Bool
afterElse [] = True
afterElse (l:ls)
  | "    " `isPrefixOf` l = afterElse ls
  | otherwise             = False   -- anything after else body = multiple blocks

-- | Collapse `else: if` into `elif` only when the else-branch is a single if-block.
mergeElif :: [String] -> [String]
mergeElif stmts@(ifLine:rest) | "if " `isPrefixOf` ifLine && isSingleIfBlock stmts =
  ("elif " ++ drop 3 ifLine) : rest
mergeElif stmts = "else:" : indentOnce stmts

-- | The else part of an @if@ statement whose else branch is @right@, rendered
-- by @gen@ (the branch's statement generator, 'generateStatementBlock' or
-- 'generateLetInStatement' at the same target): what @mergeElif@ makes of
-- @gen right >>= hoistDeepBlock right target@, without its scan.
--
-- 'mergeElif' has to scan the whole branch to see that it is one @if@
-- block, so applied at every level of an @else: if@ chain it is quadratic in
-- the chain's length -- a V-value enumeration's index chain, V = 50257 for a
-- vocabulary (task neural-int-read-compile-quadratic-in-domain). But when the
-- branch is itself an 'IRIf', @gen@ renders it as @condStmts ++ [if c:] ++
-- indented arm ++ its own else part@, which is a single @if@ block exactly
-- when its condition needs no prefix statements; so this decides that from
-- @condStmts@ instead, running the same generators in the same order (the
-- variable supply sees the same calls). While a method is being regenerated
-- with deep blocks hoisted ('stHoistDeeperThan'), the whole branch may be
-- hoisted, so that case keeps the plain route.
elseBranch :: (IRExpr -> GlobalVariableSupply [String]) -> Maybe String -> IRExpr -> GlobalVariableSupply [String]
elseBranch gen target right = do
  hoisting <- gets (isJust . stHoistDeeperThan)
  case right of
    IRIf cond l r | not hoisting -> do
      (condStmts, c) <- liftedLine cond
      lStmts <- gen l >>= hoistDeepBlock l target
      rest <- elseBranch gen target r
      let arm = indentOnce lStmts ++ rest
      return $ if null condStmts
        then ("elif " ++ c ++ ":") : arm
        else "else:" : indentOnce (condStmts ++ ["if " ++ c ++ ":"] ++ arm)
    _ -> mergeElif <$> (gen right >>= hoistDeepBlock right target)

containsIf :: IRExpr -> Bool
containsIf (IRIf _ _ _)    = True
containsIf (IROp _ l r)    = containsIf l || containsIf r
containsIf (IRUnaryOp _ e) = containsIf e
containsIf (IRApply f x)   = containsIf f || containsIf x
containsIf (IRLetIn _ v b) = containsIf v || containsIf b
containsIf (IRDensity _ _ x) = containsIf x
containsIf (IRCumulative _ _ x) = containsIf x
containsIf (IRBuiltin BMapList [f, x])   = containsIf f || containsIf x
containsIf (IRBuiltin BListIndex [l, i]) = containsIf l || containsIf i
containsIf (IRConstruct _ args) = any containsIf args
containsIf (IRDestruct _ x)     = containsIf x
containsIf _               = False

-- | Like generateExpression, but lifts complex IRIf nodes into temp variables,
-- returning prefix statements and the resulting expression.
--
-- The expression is built as a difference string (ShowS): the optimizer emits
-- world-sum spines as right-nested chains thousands of nodes deep, and plain
-- @chain ++ ")"@ concatenation re-wraps the whole suffix at every level, which
-- made rendering quadratic in chain length.  'renderLifted' forces the final
-- String exactly once per emitted statement.
generateExpressionLifted :: IRExpr -> GlobalVariableSupply ([String], ShowS)
generateExpressionLifted expr@(IRIf cond left right)
  | not (containsIf left || containsIf right) = do
      (condStmts, c) <- generateExpressionLifted cond
      l <- generateExpression left
      r <- generateExpression right
      return (condStmts, str "(" . str l . str " if " . c . str " else " . str r . str ")")
  | otherwise = do
      tmpId <- lift demandUniqueNumber
      let tmp = "_t" ++ show tmpId
      stmts <- generateLetInStatement tmp expr
      return (stmts, str tmp)
generateExpressionLifted (IRLetIn name val body) = do
  valStmts <- generateLetInStatement name val
  (bodyStmts, bodyExpr) <- generateExpressionLifted body
  return (valStmts ++ bodyStmts, bodyExpr)
generateExpressionLifted (IROp OpApprox l r) = do
  (ls, le) <- generateExpressionLifted l
  (rs, re) <- generateExpressionLifted r
  return (ls ++ rs, str "isclose(" . le . str ", " . re . str ")")
-- 'OpMax' has no infix spelling; Python's builtin `max` is the prefix form.
generateExpressionLifted (IROp OpMax l r) = do
  (ls, le) <- generateExpressionLifted l
  (rs, re) <- generateExpressionLifted r
  return (ls ++ rs, str "max(" . le . str ", " . re . str ")")
generateExpressionLifted (IROp op l r) = do
  (ls, le) <- generateExpressionLifted l
  (rs, re) <- generateExpressionLifted r
  return (ls ++ rs, str "(" . le . str " " . str (pyOps op) . str " " . re . str ")")
generateExpressionLifted (IRUnaryOp op e) = do
  (ss, se) <- generateExpressionLifted e
  return (ss, pyUnary op (str (pyUnaryOps op) . str "(" . se . str ")"))
  where pyUnary OpNot s = str "(" . s . str ")"
        pyUnary _ s = s
generateExpressionLifted (IRDensity dist Linear x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str ("density_" ++ pyDistName dist) . str "(" . sx . str ")")
generateExpressionLifted (IRCumulative dist Linear x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str ("cumulative_" ++ pyDistName dist) . str "(" . sx . str ")")
generateExpressionLifted (IRDensity dist Log x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str ("log_density_" ++ pyDistName dist) . str "(" . sx . str ")")
generateExpressionLifted (IRCumulative dist Log x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str ("log_cumulative_" ++ pyDistName dist) . str "(" . sx . str ")")
generateExpressionLifted (IRBuiltin BMapList [f, x]) = do
  (fs, fe) <- generateExpressionLifted f
  (xs, xe) <- generateExpressionLifted x
  return (fs ++ xs, str "mapList(" . fe . str ", " . xe . str ")")
generateExpressionLifted (IRBuiltin BListIndex [lst, idx]) = do
  (ls, le) <- generateExpressionLifted lst
  (is, ie) <- generateExpressionLifted idx
  return (ls ++ is, str "(" . le . str ")[" . ie . str "]")
generateExpressionLifted (IRConstruct TgTuple [f, s]) = do
  (fs, fe) <- generateExpressionLifted f
  (ss, se) <- generateExpressionLifted s
  return (fs ++ ss, str "T(" . fe . str ", " . se . str ")")
generateExpressionLifted (IRConstruct TgCons [hd, tl]) = do
  (hs, he) <- generateExpressionLifted hd
  (ts, te) <- generateExpressionLifted tl
  return (hs ++ ts, str "ConsInferenceList(" . he . str ", " . te . str ")")
generateExpressionLifted (IRConstruct TgLeft [x]) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "Left(" . sx . str ")")
generateExpressionLifted (IRConstruct TgRight [x]) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "Right(" . sx . str ")")
generateExpressionLifted (IRDestruct AcFst x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str "[0]")
generateExpressionLifted (IRDestruct AcSnd x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str "[1]")
generateExpressionLifted (IRDestruct AcHead x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str "[0]")
generateExpressionLifted (IRDestruct AcTail x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str "[1:]")
generateExpressionLifted (IRDestruct AcFromLeft x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "fromLeft(" . sx . str ")")
generateExpressionLifted (IRDestruct AcFromRight x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "fromRight(" . sx . str ")")
generateExpressionLifted (IRDestruct AcIsLeft x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "isinstance(" . sx . str ", Left)")
generateExpressionLifted (IRDestruct AcIsRight x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "isinstance(" . sx . str ", Right)")
generateExpressionLifted (IRDestruct (AcTheta i) x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str ("[0][" ++ show i ++ "]"))
generateExpressionLifted (IRDestruct (AcSubtree i) x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str ("[1][" ++ show i ++ "]"))
generateExpressionLifted expr@(IRApply _ _) = do
  let (fn, args) = collectApplyChain expr
  (fss, fn') <- generateExpressionLifted fn
  argResults <- mapM generateExpressionLifted args
  let argStmts = concatMap fst argResults
      args'    = map snd argResults
      sep = str ", "
  return (fss ++ argStmts, fn' . str "(" . foldr (.) id (intersperse sep args') . str ")")
generateExpressionLifted expr = do
  e <- generateExpression expr
  return ([], str e)

-- | Diagnostics for the tensor ranks and axes the backends do not emit. Shared
-- by all three scalar-ish backends via their own copies of the guard; the
-- message names the node so a future higher-rank producer fails with a pointer
-- rather than a mystery.
rankUnsupported :: String -> Int -> String
rankUnsupported what r =
  what ++ ": only rank-1 tensors are emitted, got rank " ++ show r
       ++ " (the representation admits it; no backend lowers it yet)"

axisUnsupported :: String -> Int -> String
axisUnsupported what ax =
  what ++ ": only axis 0 is emitted, got axis " ++ show ax
       ++ " (the representation admits it; no backend lowers it yet)"

-- | The Python runtime function reducing a tensor axis with each operator.
-- sum/max are Python's own builtins (both take an iterable, same as
-- logsumexp's own signature below), logsumexp is pythonLib.py's. max on an
-- empty iterable raises in real Python, so the call site passes
-- @default=-inf@, the interpreter's 'reduceIdentity'.
pyReduceOp :: ReduceOp -> String
pyReduceOp ROpAdd = "sum"
pyReduceOp ROpLogSumExp = "logsumexp"
pyReduceOp ROpMax = "max"

str :: String -> ShowS
str = showString

-- | Force a lifted expression into the single String it is emitted into.
renderLifted :: ShowS -> String
renderLifted e = e ""

generateStatementBlock :: IRExpr -> GlobalVariableSupply [String]
generateStatementBlock (IRLetIn name x body) = do
  s1 <- generateLetInStatement name x
  s2 <- generateStatementBlock body
  return (s1 ++ s2)
generateStatementBlock (IRIf cond left right) = do
  (condStmts, cCond) <- liftedLine cond
  cLeft  <- generateStatementBlock left >>= hoistDeepBlock left Nothing
  cRight <- elseBranch generateStatementBlock Nothing right
  let l1 = "if " ++ cCond ++ ":"
  return $ condStmts ++ [l1] ++ indentOnce cLeft ++ cRight
generateStatementBlock (IRConstruct TgTuple [IRConstruct TgTuple [f, s], bc]) = do
  fStmts  <- generateLetInStatement "_r0" f
  sStmts  <- generateLetInStatement "_r1" s
  bcStmts <- generateLetInStatement "_r2" bc
  return (fStmts ++ sStmts ++ bcStmts ++ ["return T(T(_r0, _r1), _r2)"])
generateStatementBlock (IRConstruct TgTuple [f, s]) = do
  fStmts <- generateLetInStatement "_r0" f
  sStmts <- generateLetInStatement "_r1" s
  return (fStmts ++ sStmts ++ ["return T(_r0, _r1)"])
generateStatementBlock expr = do
  (stmts, e) <- liftedLine expr
  return (stmts ++ ["return " ++ e])


generateLetInStatement :: String -> IRExpr -> GlobalVariableSupply [String]
generateLetInStatement name lmd@(IRLambda _ _) =
  generateFunction False (name, (lmd, "Inner function: " ++ name))
generateLetInStatement name (IRIf cond left right) = do
  (condStmts, c) <- liftedLine cond
  leftStmts  <- generateLetInStatement name left >>= hoistDeepBlock left (Just name)
  rightStmts <- elseBranch (generateLetInStatement name) (Just name) right
  return $ condStmts ++ ["if " ++ c ++ ":"] ++ indentOnce leftStmts ++ rightStmts
generateLetInStatement name (IRConstruct TgTuple [f, s]) = do
  fStmts <- generateLetInStatement (name ++ "_0") f
  sStmts <- generateLetInStatement (name ++ "_1") s
  return (fStmts ++ sStmts ++ [name ++ " = T(" ++ name ++ "_0, " ++ name ++ "_1)"])
generateLetInStatement name (IRLetIn innerName innerVal body) = do
  innerStmts <- generateLetInStatement innerName innerVal
  bodyStmts  <- generateLetInStatement name body
  return (innerStmts ++ bodyStmts)
generateLetInStatement name x = do
  (stmts, expr) <- liftedLine x
  return (stmts ++ [name ++ " = " ++ expr])

-- | Render one line's expression, spilling it first if the plain rendering
-- would be deeper than Python accepts. Returns the prefix statements and the
-- rendered expression.
liftedLine :: IRExpr -> GlobalVariableSupply ([String], String)
liftedLine e = do
  (stmts, se) <- generateExpressionLifted e
  let rendered = renderLifted se
  if not (tooDeepForPython rendered)
    then return (stmts, rendered)
    else do
      callables <- gets stCallables
      adtCalls <- gets stAdtCalls
      (binds, e') <- lift (spillDeep callables adtCalls e)
      if null binds
        -- Nothing strict and pure to cut out; emit as before rather than loop.
        then return (stmts, rendered)
        else do
          -- Each binding is a strictly smaller subterm, and goes through
          -- 'generateLetInStatement' (hence through here) on its own.
          bindStmts <- concat <$> mapM (uncurry generateSpillStatement) binds
          (stmts', se') <- generateExpressionLifted e'
          return (bindStmts ++ stmts', renderLifted se')

-- | Emit one spill binding. A comprehension ('spillable' admits pure ones)
-- becomes
--
-- > name = []
-- > for _vN in <list>:
-- >     <body as statements, into _eN>
-- >     name.append(_eN)
--
-- which evaluates the list once and the body once per element, in order,
-- exactly as the comprehension did, and builds the same list -- so a
-- surrounding @sum(name)@ adds the same floats in the same order. The body
-- goes through 'generateLetInStatement', so its lets become statements, its
-- conditionals @if@/@else@ blocks with the lets inside their arms (still
-- guarded), and each resulting line is measured and spilled on its own.
--
-- The loop variable is renamed to a fresh @_vN@: a @for@ target, unlike a
-- comprehension's, is bound in the enclosing function, and would otherwise
-- clobber an outer variable of the same name. (The body's own lets already
-- bound function-level names as walruses, so they are unaffected.)
--
-- Anything else is an ordinary let-binding.
generateSpillStatement :: String -> IRExpr -> GlobalVariableSupply [String]
generateSpillStatement name (IRBuiltin BMap [IRLambda v body, t]) = do
  (tStmts, tt) <- liftedLine t
  n <- lift demandUniqueNumber
  let loopVar = "_v" ++ show n
      elemVar = "_e" ++ show n
  let body' = renameFree v loopVar body
  bodyStmts <- generateLetInStatement elemVar body' >>= hoistDeepBlock body' (Just elemVar)
  return (tStmts ++ [name ++ " = []", "for " ++ loopVar ++ " in " ++ tt ++ ":"]
          ++ indentOnce (bodyStmts ++ [name ++ ".append(" ++ elemVar ++ ")"]))
generateSpillStatement name e = generateLetInStatement name e

generateExpression :: IRExpr -> GlobalVariableSupply String
generateExpression (IRIf cond left right) = do
  l <- generateExpression left
  c <- generateExpression cond
  r <- generateExpression right
  return ("(" ++ l ++ " if " ++ c ++ " else " ++ r ++ ")")
generateExpression (IROp OpApprox left right) = do
  l <- generateExpression left
  r <- generateExpression right
  return ("isclose(" ++ l ++ ", " ++ r ++ ")")
generateExpression (IROp OpMax left right) = do
  l <- generateExpression left
  r <- generateExpression right
  return ("max(" ++ l ++ ", " ++ r ++ ")")
generateExpression (IROp op left right) = do
  l <- generateExpression left
  r <- generateExpression right
  return ("(" ++ l ++ " " ++ pyOps op ++ " " ++ r ++ ")")
generateExpression (IRUnaryOp op expr) = do
  e <- generateExpression expr
  -- Python's @not@ is an operator binding looser than @==@, so @x == not(b)@
  -- is a SyntaxError; the call-like spelling needs its own parentheses. The
  -- other unary ops are function calls and bind tightly already.
  return (case op of
            OpNot -> "(" ++ pyUnaryOps op ++ "(" ++ e ++ "))"
            _     -> pyUnaryOps op ++ "(" ++ e ++ ")")
generateExpression (IRConst v) =
  return (pyVal v)
generateExpression (IRBuiltin BMapList [f, x]) = do
  ff <- generateExpression f
  xx <- generateExpression x
  return ("mapList(" ++ ff ++ ", " ++ xx ++ ")")
generateExpression (IRConstruct TgTuple [f, s]) = do
  ff <- generateExpression f
  ss <- generateExpression s
  return ("T(" ++ ff ++ ", " ++ ss ++ ")")
generateExpression (IRConstruct TgCons [hd, tl]) = do
  h <- generateExpression hd
  t <- generateExpression tl
  return ("ConsInferenceList(" ++ h ++ ", " ++ t ++ ")")
generateExpression (IRConstruct TgLeft [x]) = do
  sx <- generateExpression x
  return ("Left(" ++ sx ++ ")")
generateExpression (IRConstruct TgRight [x]) = do
  sx <- generateExpression x
  return ("Right(" ++ sx ++ ")")
generateExpression (IRDestruct AcFst x) = do
  sx <- generateExpression x
  return (sx ++ "[0]")
generateExpression (IRDestruct AcSnd x) = do
  sx <- generateExpression x
  return (sx ++ "[1]")
generateExpression (IRDestruct AcHead x) = do
  sx <- generateExpression x
  return (sx ++ "[0]")
generateExpression (IRDestruct AcTail x) = do
  sx <- generateExpression x
  return (sx ++ "[1:]")
generateExpression (IRDestruct AcFromLeft x) = do
  sx <- generateExpression x
  return ("fromLeft(" ++ sx ++ ")")
generateExpression (IRDestruct AcFromRight x) = do
  sx <- generateExpression x
  return ("fromRight(" ++ sx ++ ")")
generateExpression (IRDestruct AcIsLeft x) = do
  sx <- generateExpression x
  return ("isinstance(" ++ sx ++ ", Left)")
generateExpression (IRDestruct AcIsRight x) = do
  sx <- generateExpression x
  return ("isinstance(" ++ sx ++ ", Right)")
generateExpression (IRDestruct (AcTheta i) x) = do
  sx <- generateExpression x
  return (sx ++ "[0][" ++ show i ++ "]")
generateExpression (IRDestruct (AcSubtree i) x) = do
  sx <- generateExpression x
  return (sx ++ "[1][" ++ show i ++ "]")
generateExpression (IRDensity dist Linear x) = do
  sx <- generateExpression x
  return ("density_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
generateExpression (IRCumulative dist Linear x) = do
  sx <- generateExpression x
  return ("cumulative_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
generateExpression (IRDensity dist Log x) = do
  sx <- generateExpression x
  return ("log_density_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
generateExpression (IRCumulative dist Log x) = do
  sx <- generateExpression x
  return ("log_cumulative_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
generateExpression (IRSample IRNormal) =
  return "randn()"
generateExpression (IRSample IRUniform) =
  return "rand()"
generateExpression (IRVar name) = do
  callables <- gets stCallables
  return $ if name `elem` callables then "(" ++ name ++ ")()" else name
generateExpression expr@(IRLambda _ _) =
  generateLambdaExpression expr
generateExpression expr@(IRApply _ _) = do
  let (fn, args) = collectApplyChain expr
  fn' <- generateExpression fn
  args' <- mapM generateExpression args
  return (fn' ++ "(" ++ intercalate ", " args' ++ ")")
generateExpression (IRIsPossible multiVal expr) = do
  e <- generateExpression expr
  varName <- addOrGetFromGlobalStorage multiVal
  return ("isPossible(self." ++ varName ++ ", " ++ e ++ ")")
generateExpression (IRBuiltin BListIndex [lst, idx]) = do
  l <- generateExpression lst
  i <- generateExpression idx
  return ("(" ++ l ++ ")[" ++ i ++ "]")
generateExpression (IRLetIn name val body) = do
  v <- generateExpression val
  b <- generateExpression body
  return ("((" ++ name ++ ":=" ++ v ++ "), " ++ b ++ ")[1]")
-- The tensor builtins (design ir-tensor-values). A scalar-mode tensor is a
-- flat Python list: scalar pythonLib.py is pure-Python (probabilities are
-- floats, there is no torch in scope), so there is no real tensor to lower a
-- "tensor of primitive" to here -- that specialization lives in the batched
-- backend, where an element is a [B] tensor and a reduce really is a stacked
-- sum. What scalar mode does get is an O(1) BIndex, against BListIndex's cons
-- walk.
--
-- Only rank 1 is emitted. The representation admits any rank, but nothing
-- produces a higher-rank tensor yet and untested stride arithmetic in three
-- backends would be dead weight; the guard says so rather than emitting
-- something plausible and wrong.
generateExpression (IRBuiltin (BTensor sh) elems)
  | shapeRank sh == 1 = do
      es <- mapM generateExpression elems
      return ("[" ++ intercalate ", " es ++ "]")
  | otherwise = error (rankUnsupported "BTensor" (shapeRank sh))
-- A comprehension rather than map(lambda ...): it binds the loop variable
-- directly, saving a Python call per element, and the bound name is already a
-- valid identifier.
-- The element positions as a flat list of ints: rank 1, as for 'BTensor'.
generateExpression (IRBuiltin (BIota sh) [])
  | shapeRank sh == 1 = return ("list(range(" ++ show (shapeNumel sh) ++ "))")
  | otherwise = error (rankUnsupported "BIota" (shapeRank sh))
generateExpression (IRBuiltin BMap [IRLambda v body, t]) = do
  b <- generateExpression body
  tt <- generateExpression t
  boundIterable tt (\it -> "[" ++ b ++ " for " ++ v ++ " in " ++ it ++ "]")
generateExpression (IRBuiltin BMap [f, t]) = do
  ff <- generateExpression f
  tt <- generateExpression t
  return ("list(map(" ++ ff ++ ", " ++ tt ++ "))")
generateExpression (IRBuiltin (BReduce op ax) [t])
  | ax == 0 = do
      tt <- generateExpression t
      -- max of an empty tensor is the identity -inf (interpreter, Julia's
      -- init=-Inf), not Python's ValueError.
      let dflt = if op == ROpMax then ", default=" ++ pyDouble (-1 / 0) else ""
      return (pyReduceOp op ++ "(" ++ tt ++ dflt ++ ")")
  | otherwise = error (axisUnsupported "BReduce" ax)
generateExpression (IRBuiltin (BIndex ax) [t, k])
  | ax == 0 = do
      tt <- generateExpression t
      kk <- generateExpression k
      return ("(" ++ tt ++ ")[" ++ kk ++ "]")
  | otherwise = error (axisUnsupported "BIndex" ax)
-- Elementwise zip of two equal-length rank-1 tensors (task
-- categorical-product-ov-fusion). A comprehension over `zip`, for the same
-- reason BMap is a comprehension rather than `map(lambda ...)`: it binds the
-- two element names directly instead of paying a Python call per element.
--
-- The names are generated rather than fixed so a nested BZip (the agreement
-- fusion emits `(ta * tb) * tT`) cannot shadow the outer one's bindings.
generateExpression (IRBuiltin (BZip op) [a, b]) = do
  aa <- generateExpression a
  bb <- generateExpression b
  n <- lift demandUniqueNumber
  let (x, y) = ("_z" ++ show n ++ "a", "_z" ++ show n ++ "b")
  boundIterable ("zip(" ++ aa ++ ", " ++ bb ++ ")")
    (\it -> "[((" ++ x ++ ") " ++ pyOps op ++ " (" ++ y ++ ")) for "
            ++ x ++ ", " ++ y ++ " in " ++ it ++ "]")
-- Inverse-CDF categorical draw (task neural-categorical-sampler-nests-v-deep):
-- one runtime call, so the emitted text is O(1) in the domain size and adds no
-- nesting, where the if-chain it replaces was one indentation level per value.
generateExpression (IRBuiltin (BCategoricalIndex start n) [u, w]) = do
  uu <- generateExpression u
  ww <- generateExpression w
  return ("categorical_index(" ++ uu ++ ", " ++ ww ++ ", " ++ show start ++ ", " ++ show n ++ ")")
generateExpression (IRError e) =
  return ("throw(\"" ++ escapeStr e ++ "\")")
-- The check splices its operand textually, and a list or tensor check splices
-- it into a comprehension's iterable, so there an operand carrying a let is
-- bound once first (see 'bindIterable').
generateExpression (IRConformsTo t x) = do
  sx <- generateExpression x
  if checksElements t then boundIterable sx (pyConforms t) else return (pyConforms t sx)
generateExpression x =
  error ("Unknown expression in PyTorch codegen: " ++ show x)

-- | Escape a Haskell string for embedding in a double-quoted target-language
-- string literal (e.g. an IRError message that may contain quotes from a show'd type).
escapeStr :: String -> String
escapeStr = concatMap esc
  where esc '"'  = "\\\""
        esc '\\' = "\\\\"
        esc '\n' = "\\n"
        esc c    = [c]

-- | A runtime type-tag check for the query-type guard (see IRConformsTo). Full-depth
-- structural check mirroring the interpreter's 'valueConformsTo': recurses into tuple
-- components, either arms, and every list element; precise for float/bool/int and
-- permissive ("True") only for types with no cheap runtime tag (so it never falsely
-- rejects). The marginal-query wildcard (isAny) is accepted at every level, matching
-- VAny, and short-circuits before any component accessor is evaluated. The Int arg is
-- a nesting depth used to name list-comprehension binders uniquely.
pyConforms :: RType -> String -> String
pyConforms = pyConformsAt 0

pyConformsAt :: Int -> RType -> String -> String
pyConformsAt d t e = "(isAny(" ++ e ++ ") or " ++ pyConformsShape d t e ++ ")"

pyConformsShape :: Int -> RType -> String -> String
pyConformsShape _ TFloat  e = "isFloat(" ++ e ++ ")"
pyConformsShape _ TBool   e = "isinstance(" ++ e ++ ", bool)"
pyConformsShape _ TInt    e = "(isinstance(" ++ e ++ ", int) and not isinstance(" ++ e ++ ", bool))"
pyConformsShape d (Tuple a b) e =
  "(isinstance(" ++ e ++ ", T) and " ++ pyConformsAt d a (pyAttrBase e ++ ".t1") ++ " and " ++ pyConformsAt d b (pyAttrBase e ++ ".t2") ++ ")"
pyConformsShape d (ListOf t) e =
  let v = "_ce" ++ show d
  in "(isinstance(" ++ e ++ ", InferenceList) and all(" ++ pyConformsAt (d + 1) t v ++ " for " ++ v ++ " in " ++ e ++ "))"
pyConformsShape d (TEither a b) e =
  "((isinstance(" ++ e ++ ", Left) and " ++ pyConformsAt d a (pyAttrBase e ++ ".val") ++ ") or (isinstance(" ++ e ++ ", Right) and " ++ pyConformsAt d b (pyAttrBase e ++ ".val") ++ "))"
pyConformsShape d (TTensor sh t) e
  | shapeRank sh == 1 =
      let v = "_ce" ++ show d
      in "(isinstance(" ++ e ++ ", list) and len(" ++ e ++ ") == " ++ show (shapeNumel sh)
         ++ " and all(" ++ pyConformsAt (d + 1) t v ++ " for " ++ v ++ " in " ++ e ++ "))"
pyConformsShape _ _ _ = "True"

-- | An operand as the base of an attribute access (@e.t1@): a number
-- literal is parenthesised, since @3.t1@ does not parse and @-3.t1@ reads as
-- @-(3.t1)@ (task ir-conformsto-lowering-gaps-in-text-backends). Anything
-- else is emitted as it was: a name or a call is already a primary, and the
-- generator parenthesises its operator and conditional expressions.
pyAttrBase :: String -> String
pyAttrBase e@(c : _) | c == '-' || isDigit c = "(" ++ e ++ ")"
pyAttrBase e = e

-- | Whether 'pyConforms' iterates over (a component of) its operand.
checksElements :: RType -> Bool
checksElements (ListOf _) = True
checksElements (TTensor _ _) = True
checksElements (Tuple a b) = checksElements a || checksElements b
checksElements (TEither a b) = checksElements a || checksElements b
checksElements _ = False


-- | 'bindIterable' with a fresh temporary, drawn only when the iterable needs
-- one, so the numbering of every other generated name is unchanged.
boundIterable :: String -> (String -> String) -> GlobalVariableSupply String
boundIterable it comp
  | hasAssignmentExpr it = do
      n <- lift demandUniqueNumber
      return (bindIterable ("_it" ++ show n) it comp)
  | otherwise = return (comp it)

generateLambdaExpression :: IRExpr -> GlobalVariableSupply String
generateLambdaExpression expr = do
  let (names, rest) = getLambdaNames expr
  body <- generateExpression rest
  return ("(lambda " ++ intercalate ", " names ++ ": " ++ body ++ ")")

getLambdaNames :: IRExpr -> ([String], IRExpr)
getLambdaNames (IRLambda n body) = (n:names, rest)
  where (names, rest) = getLambdaNames body
getLambdaNames x = ([], x)