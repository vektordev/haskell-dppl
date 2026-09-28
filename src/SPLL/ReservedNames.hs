-- | The single authority for names the pipeline claims (design
-- @reserved-name-registry@).
--
-- The compiler generates names of its own -- the query parameter of every
-- probability function, IR temporaries, the per-function variant names, the
-- extra groups AutoNeural and the extra semirings add -- and it emits the
-- user's names into target languages that have reserved words of their own. A
-- user identifier that lands on one of those names used to be accepted and then
-- misbehave: a parameter called @sample@ was captured by the generated query
-- binder (the interpreter answered the density at the wrong point; Python and
-- Julia refused the module for a duplicate argument), a local called @b_gen@
-- was taken for a generator call and the program refused as
-- "draws randomness", and a function called @n_auto@ beside a network @n@
-- emitted two Python classes of which the second silently won.
--
-- This module owns every such list, and nothing here imports anything from
-- the compiler, so any stage can consume it. Two kinds of claim live here and
-- they are treated differently:
--
-- * __SPLL-internal names__ ('reservedIdentifierReason',
--   'groupNameCollisions'): names the compiler itself generates. A user
--   identifier matching one is /rejected/ by 'SPLL.Validator.validateProgram',
--   independently of the target, because the collision is in the compiler's
--   own namespace.
--
-- * __Target-language keywords__ ('pythonKeywords', 'juliaKeywords'): a name
--   legal in SPLL that the target cannot spell. These are /mangled/ at
--   emission rather than rejected (task
--   @codegen-adt-name-collides-with-target-keyword@): whether a program is
--   legal must not depend on which backend it is aimed at.
--
-- Adding a new generated name anywhere in the pipeline means adding it here.
-- @TestInternals@'s @reserved names@ group compiles a program using every
-- entry and asserts the refusal, so an entry cannot silently stop being
-- checked.
module SPLL.ReservedNames
  ( -- * Surface-language keywords
    languageKeywords
    -- * Distribution primitives
  , uniformName
  , normalName
  , distributionPrimitiveNames
    -- * Names the compiler binds in generated code
  , queryParamName
  , accProbParamName
  , topKCutoffName
  , accProbInitName
    -- * Per-function variant suffixes
  , genSuffix
  , probSuffix
  , integSuffix
  , writeLogitsSuffix
  , normalSuffix
  , functionVariantSuffixes
    -- * Group-name suffixes
  , neuralReadLogitsSuffix
  , maxProductGroupTag
  , countingGroupTag
  , sumProductGroupTag
    -- * The user-identifier checks
  , destructBinderPrefix
  , observeBinderPrefix
  , reservedIdentifierReason
  , internalNameReason
  , groupNameCollisions
    -- * Target-language keywords
  , pythonKeywords
  , pythonRuntimeClassNames
  , pythonReservedIdentifiers
  , juliaKeywords
  ) where

import Data.Char (isDigit)
import Data.List (isPrefixOf, isSuffixOf, find)

-- ---------------------------------------------------------------------------
-- Surface-language keywords

-- | Words the parser refuses as an identifier ('SPLL.Parser.pIdentifier').
-- Includes the distribution primitives, which the parser reads as their own
-- productions.
languageKeywords :: [String]
languageKeywords =
  [ "data", "if", "then", "else", "let", "draw", "define", "in", "theta"
  , "subtree", "error", "observe", "ThetaTree", "Left", "Right", "Real" ]
  ++ distributionPrimitiveNames

-- ---------------------------------------------------------------------------
-- Distribution primitives

uniformName, normalName :: String
uniformName = "Uniform"
normalName  = "Normal"

-- | The built-in distribution primitives: a @Var@ of one of these names is a
-- fresh draw, not a reference. Every stage that needs the /set/ (the
-- validator's declared-name check, RInfer's environment, Determinism's random
-- anchors, the parser's keywords) reads it from here; a stage that dispatches
-- on the individual primitive uses 'uniformName'/'normalName'.
distributionPrimitiveNames :: [String]
distributionPrimitiveNames = [uniformName, normalName]

-- ---------------------------------------------------------------------------
-- Names the compiler binds in generated code

-- | The query-point parameter of every compiled probability and integrate
-- function (IRCompiler, AutoNeural). A user binder of this name is captured by
-- it.
queryParamName :: String
queryParamName = "sample"

-- | The accumulated-path-probability parameter a topK compile adds to every
-- probability function.
accProbParamName :: String
accProbParamName = "acc_prob"

-- | The topK cutoff constant ('SPLL.IntermediateRepresentation.IREnv' consts).
topKCutoffName :: String
topKCutoffName = "TOP_K_CUTOFF"

-- | The initial accumulated probability a topK compile passes at the root.
accProbInitName :: String
accProbInitName = "ACC_PROB_INIT"

-- | Exact names, each with the reason it is claimed.
reservedExactNames :: [(String, String)]
reservedExactNames =
  [ (queryParamName,   "it is the query parameter of every compiled probability and integrate function")
  , (accProbParamName, "it is the accumulated-probability parameter of a topK-pruned probability function")
  , (topKCutoffName,   "it is the constant holding the topK pruning threshold")
  , (accProbInitName,  "it is the constant holding a topK compile's initial accumulated probability")
  ]

-- | Name prefixes, each with the reason it is claimed.
--
-- The leading underscore is a blanket claim rather than a list: the Python
-- backends emit a family of underscore temporaries (@_r0@, @_s3@, @_z@,
-- @_batchN@, ...) that grows with the backends, and a list of them would be
-- stale the day a new one was added.
reservedPrefixes :: [(String, String)]
reservedPrefixes =
  [ ("l_",   "the prefix 'l_' is reserved for the compiler's IR temporaries")
  , ("cse_", "the prefix 'cse_' is reserved for the optimizer's shared subexpressions")
  , ("_",    "identifiers beginning with '_' are reserved for temporaries in the generated code")
  ]

-- | A prefix followed by at least one digit (and then anything): forward
-- chaining's chain names (@ast12@), which the higher-order inverse binds as IR
-- lambda parameters.
reservedNumberedPrefixes :: [(String, String)]
reservedNumberedPrefixes =
  [ ("ast", "names 'ast<number>' are the compiler's chain names, which it binds in generated code") ]

-- | The binders the /parser/ generates while desugaring: @p_d<n>@ for a
-- destructuring @h : t@ pattern, @p_ob<n>@ for @observe@'s bound base.
destructBinderPrefix, observeBinderPrefix :: String
destructBinderPrefix = "p_d"
observeBinderPrefix  = "p_ob"

-- | Unlike every other entry these legitimately occur in an AST -- the parser
-- put them there -- so only the surface check ('reservedIdentifierReason')
-- refuses them, and the AST-level one ('internalNameReason') does not.
parserBinderPrefixes :: [(String, String)]
parserBinderPrefixes =
  [ (destructBinderPrefix, "names 'p_d<number>' are the binders the parser generates for destructuring patterns")
  , (observeBinderPrefix,  "names 'p_ob<number>' are the binders the parser generates for observe")
  ]

-- ---------------------------------------------------------------------------
-- Per-function variant suffixes

-- | Every top-level definition @f@ compiles to up to five functions named
-- @f@ ++ one of these. Several passes also read a name's role back off its
-- suffix ('SPLL.IntermediateRepresentation.isEffectfulVar' calls every
-- @_gen@ reference a random draw, the Python backend resolves @f_prob@ to
-- @f.forward@), so a user identifier ending in one is misread wherever it
-- appears, not only where it collides with a real variant.
genSuffix, probSuffix, integSuffix, writeLogitsSuffix, normalSuffix :: String
genSuffix         = "_gen"
probSuffix        = "_prob"
integSuffix       = "_integ"
writeLogitsSuffix = "_writeLogits"
normalSuffix      = "_normal"

functionVariantSuffixes :: [String]
functionVariantSuffixes = [genSuffix, probSuffix, integSuffix, writeLogitsSuffix, normalSuffix]

-- | Suffixes beyond the variants: the inverse-derivative binder an inverted
-- user function gets (@f_prob_deriv@, IRCompiler's higher-order inverse).
extraReservedSuffixes :: [String]
extraReservedSuffixes = ["_prob_deriv"]

-- ---------------------------------------------------------------------------
-- Group-name suffixes

-- | AutoNeural's function group for a neural declaration @n@ is
-- @n ++ neuralReadLogitsSuffix@.
neuralReadLogitsSuffix :: String
neuralReadLogitsSuffix = "_auto"

-- | The tags 'SPLL.Semiring.semiringSuffix' gives each semiring family; an
-- extra-semiring compile of @f@ is the group @f_<tag>@.
maxProductGroupTag, countingGroupTag, sumProductGroupTag :: String
maxProductGroupTag = "map"
countingGroupTag   = "count"
sumProductGroupTag = "sumprod"

-- ---------------------------------------------------------------------------
-- The user-identifier checks

-- | Why a user-written identifier may not be used, or 'Nothing' if it may.
-- Applied by the parser ('SPLL.Parser.pIdentifier') to every name in the value
-- namespace: definitions, parameters and binders, references, neural
-- declarations, constructors and fields.
reservedIdentifierReason :: String -> Maybe String
reservedIdentifierReason name =
  internalNameReason name `orElse` numberedReason parserBinderPrefixes name

-- | 'reservedIdentifierReason' minus the parser's own desugaring binders: the
-- check for a name found in an already-built AST, which the parser's binders
-- legitimately inhabit. 'SPLL.Validator.validateProgram' applies it to every
-- binder and declaration, which covers programs built in Haskell rather than
-- parsed.
internalNameReason :: String -> Maybe String
internalNameReason name =
  lookup name reservedExactNames
  `orElse` (snd <$> find (\(p, _) -> p `isPrefixOf` name) reservedPrefixes)
  `orElse` numberedReason reservedNumberedPrefixes name
  `orElse` (suffixReason <$> find (`isSuffixOf` name) (extraReservedSuffixes ++ functionVariantSuffixes))
  where
    suffixReason s = "the suffix '" ++ s ++ "' is reserved for the functions the compiler derives from each definition"

numberedReason :: [(String, String)] -> String -> Maybe String
numberedReason table name = snd <$> find (numberedAfter . fst) table
  where
    numberedAfter p = p `isPrefixOf` name && startsWithDigit (drop (length p) name)
    startsWithDigit (c:_) = isDigit c
    startsWithDigit []    = False

orElse :: Maybe a -> Maybe a -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing  y = y

-- | Group names the compiler derives that would land on a user definition.
-- Takes the program's top-level function names and neural declaration names,
-- and answers each clash as @(derived group, what derives it)@.
--
-- Checked as a collision rather than a blanket suffix ban: @word_count@ or
-- @id_map@ are ordinary names, and are only a problem beside a definition
-- @word@ / @id@ whose extra-semiring group they would be. The semiring groups
-- are checked whether or not the compile requests them, so that a program's
-- legality does not depend on a CLI flag.
groupNameCollisions :: [String] -> [String] -> [(String, String)]
groupNameCollisions functionNames neuralNames =
  [ (derived, "the neural declaration '" ++ n ++ "' (its generated read-logits group)")
  | n <- neuralNames, let derived = n ++ neuralReadLogitsSuffix, derived `elem` taken ]
  ++
  [ (derived, "the definition '" ++ f ++ "' (its " ++ tag ++ "-semiring group)")
  | f <- functionNames, tag <- [maxProductGroupTag, countingGroupTag, sumProductGroupTag]
  , let derived = f ++ "_" ++ tag, derived `elem` taken ]
  where
    taken = functionNames ++ neuralNames

-- ---------------------------------------------------------------------------
-- Target-language keywords

-- | Python's hard keywords -- the names that are a @SyntaxError@ as an
-- identifier. Mangled by 'SPLL.CodeGenPyTorch.pyMangle'.
--
-- Soft keywords (@match@, @case@, @type@, @_@) are deliberately absent: they
-- are contextually valid as ordinary identifiers, so mangling them would rename
-- names that work. Names merely /exported by/ @pythonLib@ (@eq@, @T@, @isAny@,
-- ...) are also absent -- shadowing one is a real hazard but a different one,
-- and it needs the library's whole surface rather than a fixed keyword list.
pythonKeywords :: [String]
pythonKeywords =
  [ "False", "None", "True", "and", "as", "assert", "async", "await", "break"
  , "class", "continue", "def", "del", "elif", "else", "except", "finally"
  , "for", "from", "global", "if", "import", "in", "is", "lambda", "nonlocal"
  , "not", "or", "pass", "raise", "return", "try", "while", "with", "yield"
  ]

-- | The classes the emitted Python module has in scope before any of its own
-- definitions: @torch.nn.Module@, which every function group subclasses, and
-- every class @pythonLib@ / @pythonLibBatched@ define (and @typing.Iterable@,
-- which @pythonLib@'s star import re-exports). A function group's class, or an
-- ADT constructor's, spelled like one of these replaced it for the whole
-- module: a definition @t@ emitted @class T(Module)@ over the runtime's tuple
-- class, and every tuple in the program then failed with "T() takes no
-- arguments". @TestInternals@ checks this list against the class definitions
-- in both runtime files, so a new runtime class cannot be missed here.
pythonRuntimeClassNames :: [String]
pythonRuntimeClassNames =
  [ "Module", "Iterable", "T", "Left", "Right", "InferenceList"
  , "EmptyInferenceList", "AnyInferenceList", "ConsInferenceList", "EnumBatch" ]

-- | Every name 'SPLL.CodeGenPyTorch.pyMangle' escapes: the keywords, the
-- runtime classes above, and @self@, which every emitted method binds as its
-- first parameter -- a user parameter called @self@ emitted
-- @def forward(self, self, sample)@, a duplicate-argument @SyntaxError@.
--
-- Names merely /exported by/ the runtime as functions (@randn@, @isAny@, ...),
-- @math@'s star import, and Python's builtins are deliberately absent: a user
-- name shadowing one of those is a real hazard, but the list is open-ended and
-- tracked separately (docs task @python-runtime-name-shadowing@).
pythonReservedIdentifiers :: [String]
pythonReservedIdentifiers = pythonKeywords ++ ["self"] ++ pythonRuntimeClassNames

-- | Julia's reserved words. Mangled by 'SPLL.CodeGenJulia.juliaMangle'.
--
-- A field named @end@ emits @struct Mk / end / end@, which closes the struct
-- two lines early and is mis-parsed rather than rejected at the offending
-- token. Contextual keywords that are legal identifiers elsewhere (@new@,
-- @outer@, @var@, and the @abstract@/@mutable@/@primitive@ modifiers) are
-- included: mangling a name that would have worked costs nothing, while
-- missing one that would not costs a silently mis-parsed module.
juliaKeywords :: [String]
juliaKeywords =
  [ "abstract", "baremodule", "begin", "break", "catch", "const", "continue"
  , "do", "else", "elseif", "end", "export", "false", "for", "function"
  , "global", "if", "import", "in", "isa", "let", "local", "macro", "module"
  , "mutable", "new", "outer", "primitive", "quote", "return", "struct", "true"
  , "try", "type", "using", "var", "where", "while"
  ]
