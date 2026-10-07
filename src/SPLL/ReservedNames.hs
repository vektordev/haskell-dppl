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
-- * __Target-language names__ ('pythonReservedIdentifiers',
--   'juliaReservedIdentifiers'): a name legal in SPLL that the target cannot
--   spell (a keyword), or that the emitted code already uses for something
--   else (a runtime-library function, a builtin). These are /mangled/ at
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
  , topKCutoffParamName
  , accProbInitName
    -- * Per-function variant suffixes
  , genSuffix
  , probSuffix
  , integSuffix
  , writeLogitsSuffix
  , normalSuffix
  , functionVariantSuffixes
  , componentNormalGroupPrefix
  , componentNormalName
    -- * Group-name suffixes
  , neuralReadLogitsSuffix
  , perValuePointSuffix
  , perValuePriorSuffix
  , perValueGivenSuffix
  , perValueSlotSuffix
  , perValueHelperSuffixes
  , maxProductGroupTag
  , countingGroupTag
  , sumProductGroupTag
    -- * The user-identifier checks
  , destructBinderPrefix
  , observeBinderPrefix
  , etaBinderPrefix
  , reservedIdentifierReason
  , internalNameReason
  , groupNameCollisions
    -- * Target-language keywords
  , pythonKeywords
  , pythonRuntimeClassNames
  , pythonRuntimeValueNames
  , pythonBuiltinNames
  , pythonReservedIdentifiers
  , isPythonReserved
  , juliaKeywords
  , juliaRuntimeNames
  , juliaBaseNames
  , juliaReservedIdentifiers
  , isJuliaReserved
  ) where

import Data.Char (isDigit)
import Data.List (isPrefixOf, isSuffixOf, find, stripPrefix)
import qualified Data.Set as Set

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

-- | The topK cutoff constant ('SPLL.IntermediateRepresentation.IREnv' consts):
-- the compiled-in /default/ cutoff a caller passes as 'topKCutoffParamName'
-- when it has no threshold of its own (task runtime-parametric-topk-threshold).
topKCutoffName :: String
topKCutoffName = "TOP_K_CUTOFF"

-- | The runtime topK cutoff parameter a topK compile adds to every
-- probability function (after 'accProbParamName') and every integrate
-- function (after the query). Every pruning guard compares against it, so one
-- compiled artifact answers queries at any threshold chosen at call time. It
-- is in the semiring's space, like 'accProbParamName': @log t@ under logSpace.
topKCutoffParamName :: String
topKCutoffParamName = "top_k_cutoff"

-- | The initial accumulated probability a topK compile passes at the root.
accProbInitName :: String
accProbInitName = "ACC_PROB_INIT"

-- | Exact names, each with the reason it is claimed.
reservedExactNames :: [(String, String)]
reservedExactNames =
  [ (queryParamName,   "it is the query parameter of every compiled probability and integrate function")
  , (accProbParamName, "it is the accumulated-probability parameter of a topK-pruned probability function")
  , (topKCutoffName,   "it is the constant holding the default topK pruning threshold")
  , (topKCutoffParamName, "it is the runtime topK cutoff parameter of a topK-pruned probability or integrate function")
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

-- | The binders the /frontend/ generates while desugaring: @p_d<n>@ for a
-- destructuring @h : t@ pattern, @p_ob<n>@ for @observe@'s bound base (both
-- the parser), @p_eta<n>@ for the parameters of an eta-expanded point-free
-- alias (@alias = coin@, 'SPLL.CalleeNormalize').
destructBinderPrefix, observeBinderPrefix, etaBinderPrefix :: String
destructBinderPrefix = "p_d"
observeBinderPrefix  = "p_ob"
etaBinderPrefix      = "p_eta"

-- | Unlike every other entry these legitimately occur in an AST -- the
-- frontend put them there -- so only the surface check ('reservedIdentifierReason')
-- refuses them, and the AST-level one ('internalNameReason') does not.
parserBinderPrefixes :: [(String, String)]
parserBinderPrefixes =
  [ (destructBinderPrefix, "names 'p_d<number>' are the binders the parser generates for destructuring patterns")
  , (observeBinderPrefix,  "names 'p_ob<number>' are the binders the parser generates for observe")
  , (etaBinderPrefix,      "names 'p_eta<number>' are the parameters the compiler generates when eta-expanding a point-free alias")
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

-- | A tuple-shaped Gaussian function @f@ also gets one normal-parameter
-- function per component (@f_normal_fst@, @f_normal_snd@, ...), each hosted by
-- a group of its own named with this prefix (@_component_f_normal_fst@). The
-- group has no variant suffix: its normal function is referenced by the bare
-- component name, which every consumer recovers with 'componentNormalName' --
-- the interpreter's environment, AutoNeural's availability check, and the
-- Python/Julia emitters, which have to /define/ the function under the name
-- the IR calls it by (task writelogits-text-backends-broken). A leading @_@
-- is already reserved, so no user group can carry the prefix.
componentNormalGroupPrefix :: String
componentNormalGroupPrefix = "_component_"

-- | The name a component group's normal function is referenced by, or
-- 'Nothing' for an ordinary group (whose is @groupName ++ normalSuffix@).
componentNormalName :: String -> Maybe String
componentNormalName = stripPrefix componentNormalGroupPrefix

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

-- | The helper definitions a per-value function @f@ (one whose signature marks
-- a result slot @Enumerated@; task per-value-query-over-enumerated-slot,
-- "SPLL.PerValue") is compiled through:
--
-- * @f__point@ -- @f@'s own definition, answering ordinary point queries; every
--   other function's reference to @f@ is redirected to it;
-- * @f__prior@ / @f__given@ -- the fast path's split of @f@ at the draw that
--   binds the marked slot: the draw's distribution, and the rest of the body
--   with the drawn value as an extra, deterministic parameter;
-- * @f__slot@ -- the marked slot alone, read for its finite domain and never
--   compiled.
--
-- A user definition of one of these names beside a per-value @f@ is refused
-- by 'SPLL.PerValue.validateSignatures'.
perValuePointSuffix, perValuePriorSuffix, perValueGivenSuffix, perValueSlotSuffix :: String
perValuePointSuffix = "__point"
perValuePriorSuffix = "__prior"
perValueGivenSuffix = "__given"
perValueSlotSuffix  = "__slot"

perValueHelperSuffixes :: [String]
perValueHelperSuffixes = [perValuePointSuffix, perValuePriorSuffix, perValueGivenSuffix, perValueSlotSuffix]

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
-- are contextually valid as ordinary identifiers, so they are no hazard as
-- keywords (@type@ is escaped anyway, as a builtin -- see 'pythonBuiltinNames').
-- Names the runtime or Python itself binds are the other lists below.
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

-- | The non-class values the emitted Python module has in scope before any of
-- its own definitions: everything @from pythonLib import *@ and
-- @from pythonLibBatched import *@ bring in -- the runtimes' own functions and
-- constants, the modules they import, and everything @pythonLib@'s own
-- @from math import *@ re-exports -- plus the modules the emitted header
-- imports itself (@functools@, @math@, @torch@).
--
-- A user name spelled like one of these shadowed it: a parameter @randn@ made
-- the body's @Normal@ draw call the parameter ("'float' object is not
-- callable"), and a definition @randn@ emitted @randn = Randn()@ over the
-- library function at module scope (task @python-runtime-name-shadowing@).
--
-- Hand-maintained rather than derived at build time, so that the emitted code
-- does not depend on which Python the compiler was built beside. The @math@
-- entries are the union over the Pythons it was checked against (3.9, 3.13, 3.14:
-- @cbrt@, @exp2@, @fma@, @sumprod@ are newer than 3.9); listing a name a given
-- Python lacks costs only a harmless rename. @TestInternals@ asks @python3@ for
-- the runtimes' actual surface and fails on any name missing here.
pythonRuntimeValueNames :: [String]
pythonRuntimeValueNames =
  [ "DENSE_MIN_BATCH", "DTYPE", "acos", "acosh", "asin", "asinh", "asmask"
  , "astensor", "atan", "atan2", "atanh", "bucket_count", "bucketed"
  , "categorical_index", "cbrt", "ceil", "check_result", "comb", "copysign"
  , "cos", "cosh", "cumulative_normal", "cumulative_uniform", "degrees"
  , "dense_positions", "dense_query", "density_normal", "density_uniform"
  , "denskey", "dist", "e", "eq", "erf", "erfc", "exp", "exp2", "expm1"
  , "fabs", "factorial", "floor", "fma", "fmod", "frexp", "fromLeft"
  , "fromRight", "fsum", "functools", "gamma", "gather_dense", "gauss"
  , "gcd", "hypot", "indexOf", "inf", "isAny", "isPossible", "is_ctor"
  , "is_member", "isclose", "isfinite", "isinf", "isnan", "isqrt"
  , "itertools", "lcm", "ldexp", "lgamma", "listConcat", "listProd", "log", "log10"
  , "log1p", "log2", "log_cumulative_normal", "log_cumulative_uniform"
  , "log_density_normal", "log_density_uniform", "logsumexp", "mapList"
  , "math", "modf", "nan", "nextafter", "nn_gather", "perm", "pi", "poison"
  , "pow", "prod", "radians", "rand", "randn", "random", "remainder"
  , "safe_div", "safe_exp", "safe_log", "sign", "signature", "sin", "sinh"
  , "sqrt", "sumprod", "sys", "table_select", "tan", "tanh", "tau", "tensor_index"
  , "tensor_logsumexp", "tensor_sum", "throw", "toList", "torch", "trunc"
  , "ulp", "where_anchored"
  ]

-- | Python's builtins (@dir(builtins)@ without the dunders), union over the
-- same Python versions as 'pythonRuntimeValueNames' and test-synced the same
-- way.
--
-- All of them rather than only the ones the emitted code happens to call
-- today: which builtins codegen emits is not tracked anywhere and changes with
-- it, while mangling a name that would have worked costs nothing but a
-- trailing underscore. Includes the exception classes, which a group class
-- (@groupClassName@ capitalises) or a constructor could otherwise replace.
pythonBuiltinNames :: [String]
pythonBuiltinNames =
  [ "ArithmeticError", "AssertionError", "AttributeError", "BaseException"
  , "BaseExceptionGroup", "BlockingIOError", "BrokenPipeError"
  , "BufferError", "BytesWarning", "ChildProcessError"
  , "ConnectionAbortedError", "ConnectionError", "ConnectionRefusedError"
  , "ConnectionResetError", "DeprecationWarning", "EOFError", "Ellipsis"
  , "EncodingWarning", "EnvironmentError", "Exception", "ExceptionGroup"
  , "False", "FileExistsError", "FileNotFoundError", "FloatingPointError"
  , "FutureWarning", "GeneratorExit", "IOError", "ImportError"
  , "ImportWarning", "IndentationError", "IndexError", "InterruptedError"
  , "IsADirectoryError", "KeyError", "KeyboardInterrupt", "LookupError"
  , "MemoryError", "ModuleNotFoundError", "NameError", "None"
  , "NotADirectoryError", "NotImplemented", "NotImplementedError", "OSError"
  , "OverflowError", "PendingDeprecationWarning", "PermissionError"
  , "ProcessLookupError", "PythonFinalizationError", "RecursionError"
  , "ReferenceError", "ResourceWarning", "RuntimeError", "RuntimeWarning"
  , "StopAsyncIteration", "StopIteration", "SyntaxError", "SyntaxWarning"
  , "SystemError", "SystemExit", "TabError", "TimeoutError", "True"
  , "TypeError", "UnboundLocalError", "UnicodeDecodeError"
  , "UnicodeEncodeError", "UnicodeError", "UnicodeTranslateError"
  , "UnicodeWarning", "UserWarning", "ValueError", "Warning"
  , "ZeroDivisionError", "abs", "aiter", "all", "anext", "any", "ascii"
  , "bin", "bool", "breakpoint", "bytearray", "bytes", "callable", "chr"
  , "classmethod", "compile", "complex", "copyright", "credits", "delattr"
  , "dict", "dir", "divmod", "enumerate", "eval", "exec", "exit", "filter"
  , "float", "format", "frozenset", "getattr", "globals", "hasattr", "hash"
  , "help", "hex", "id", "input", "int", "isinstance", "issubclass", "iter"
  , "len", "license", "list", "locals", "map", "max", "memoryview", "min"
  , "next", "object", "oct", "open", "ord", "pow", "print", "property"
  , "quit", "range", "repr", "reversed", "round", "set", "setattr", "slice"
  , "sorted", "staticmethod", "str", "sum", "super", "tuple", "type", "vars"
  , "zip"
  ]

-- | Every name 'SPLL.CodeGenPyTorch.pyMangle' escapes: the keywords, @self@
-- (every emitted method binds it as its first parameter -- a user parameter
-- called @self@ emitted @def forward(self, self, sample)@, a duplicate-argument
-- @SyntaxError@), the runtime classes, the runtime's other values, and the
-- builtins.
--
-- None of these ends in an underscore, and 'pyMangle''s injectivity argument
-- relies on that (@TestInternals@ checks it): a reserved @x_@ would be the
-- image of a user's @x@.
pythonReservedIdentifiers :: [String]
pythonReservedIdentifiers =
  pythonKeywords ++ ["self"] ++ pythonRuntimeClassNames
  ++ pythonRuntimeValueNames ++ pythonBuiltinNames

pythonReservedSet :: Set.Set String
pythonReservedSet = Set.fromList pythonReservedIdentifiers

-- | Membership in 'pythonReservedIdentifiers', as a set lookup: the mangler
-- asks it of every identifier it prints.
isPythonReserved :: String -> Bool
isPythonReserved n = Set.member n pythonReservedSet

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

-- | Every name @juliaLib@ exports into the emitted module (its @export@ line,
-- which @TestInternals@ checks this against). @==@ is exported too but is no
-- identifier.
juliaRuntimeNames :: [String]
juliaRuntimeNames =
  [ "safe_log", "categorical_index", "density_IRUniform", "density_IRNormal"
  , "cumulative_IRUniform", "cumulative_IRNormal", "log_density_IRUniform"
  , "log_density_IRNormal", "log_cumulative_IRUniform"
  , "log_cumulative_IRNormal", "logsumexp", "isAny", "InferenceList"
  , "EmptyInferenceList", "AnyInferenceList", "ConsInferenceList", "length"
  , "getindex", "head", "tail", "prepend", "mapList", "eq", "isPossible"
  , "isclose", "indexOf", "listProd", "listConcat", "T", "Either", "Left", "Right"
  , "fromLeft", "fromRight"
  ]

-- | The names from Julia's @Base@ (and @Core@) that emitted code refers to:
-- the calls and literals 'SPLL.CodeGenJulia' prints and the types its
-- query-conformance guard tests with @isa@.
--
-- Julia has no star-import to shadow at module scope -- a definition @f@ is
-- emitted as @f_gen@, @f_prob@, ... -- so the hazard is a /local/: a parameter
-- @randn@ made the body's @Normal@ draw call the parameter ("objects of type
-- Float64 are not callable", task @python-runtime-name-shadowing@). @Base@
-- exports far too many names to list, so unlike 'pythonBuiltinNames' this is
-- the used subset. @End2EndTesting@ compiles the corpus to Julia and fails on
-- any name emitted code calls that the module neither defines nor finds here
-- or in 'juliaRuntimeNames' -- so a new call in codegen cannot be missed.
juliaBaseNames :: [String]
juliaBaseNames =
  [ "exp", "abs", "sign", "sum", "maximum", "max", "map", "all", "rand"
  , "randn", "throw", "string", "typeof", "Inf", "NaN", "nothing"
  , "AbstractFloat", "Bool", "Integer"
  ]

-- | Every name 'SPLL.CodeGenJulia.juliaMangle' escapes: the keywords, the
-- runtime's exports and the @Base@ names emitted code uses. As for Python, none
-- ends in an underscore.
juliaReservedIdentifiers :: [String]
juliaReservedIdentifiers = juliaKeywords ++ juliaRuntimeNames ++ juliaBaseNames

juliaReservedSet :: Set.Set String
juliaReservedSet = Set.fromList juliaReservedIdentifiers

-- | Membership in 'juliaReservedIdentifiers', as a set lookup.
isJuliaReserved :: String -> Bool
isJuliaReserved n = Set.member n juliaReservedSet
