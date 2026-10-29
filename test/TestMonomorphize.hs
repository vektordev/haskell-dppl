module TestMonomorphize (monomorphizeTests) where

-- Design polymorphic-monomorphization: a top-level function used at two
-- numeric types is typed by let-generalisation and cloned once per type
-- ('SPLL.Typing.Monomorphize'), where monomorphic inference used to reject the
-- program outright. Since task rinfer-generalise-unconditionally the
-- generalising inference is the only path, not a fallback, so its diagnostics
-- are the ones reported. The end-to-end values are pinned by the corpus
-- programs test/cases/arithmetic/polyTwoTypes and polyNestedTwoTypes; this
-- module pins the typing: which declarations come out, at which types, and
-- which error an ill-typed program gets.

import SPLL.Lang.Types (Program(..), Expr(..), ExprF(..), TypeInfo(..))
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.RInfer (addRTypeInfo)
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude (runGen)
import SPLL.CompilerConfig (defaultCompilerConfig)
import Control.Monad.Random.Lazy (evalRand, mkStdGen)

import Data.List (isInfixOf, sort)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool, assertFailure)

monomorphizeTests :: TestTree
monomorphizeTests = testGroup "Monomorphize"
  [ testCase "used at Float and Int: two mangled instances" $ do
      p <- typed "addTwice x = x + x\na = addTwice 1.0\nb = addTwice 1\nmain = (a, b)\n"
      assertEqual "declarations" (sort ["a", "b", "main", "addTwice__float", "addTwice__int"]) (sort (declNames p))
      assertEqual "a" TFloat (declType p "a")
      assertEqual "b" TInt (declType p "b")
      assertEqual "Float instance" (TArrow TFloat TFloat) (declType p "addTwice__float")
      assertEqual "Int instance" (TArrow TInt TInt) (declType p "addTwice__int")
      assertEqual "main" (Tuple TFloat TInt) (declType p "main")

  , testCase "used at Float only: no mangling" $ do
      p <- typed "addTwice x = x + x\nmain = addTwice 1.0\n"
      assertEqual "declarations" ["addTwice", "main"] (declNames p)
      assertEqual "addTwice" (TArrow TFloat TFloat) (declType p "addTwice")

  , testCase "used at Int only: no mangling" $ do
      p <- typed "addTwice x = x + x\nmain = addTwice 1\n"
      assertEqual "declarations" ["addTwice", "main"] (declNames p)
      assertEqual "addTwice" (TArrow TInt TInt) (declType p "addTwice")

  , testCase "a polymorphic caller instantiates its callee per instance" $ do
      p <- typed "add x y = x + y\nadd3 x y z = add (add x y) z\nmain = (add3 1.0 2.0 3.0, add3 1 2 3)\n"
      assertEqual "declarations"
        (sort ["main", "add__float", "add__int", "add3__float", "add3__int"]) (sort (declNames p))
      assertEqual "add3 at Int" (TArrow TInt (TArrow TInt (TArrow TInt TInt))) (declType p "add3__int")
      assertBool "add3__int calls add__int" ("add__int" `elem` varsOf (declBody p "add3__int"))
      assertBool "add3__float calls add__float" ("add__float" `elem` varsOf (declBody p "add3__float"))

  , testCase "self-recursion stays within its instance" $ do
      p <- typed "sumTo n acc = if n < 1 then acc else sumTo (n - 1) (acc + acc)\nmain = (sumTo 2 1.0, sumTo 2 1)\n"
      assertBool "sumTo__int recurses into itself" ("sumTo__int" `elem` varsOf (declBody p "sumTo__int"))
      assertBool "and not into the Float instance" (not ("sumTo__float" `elem` varsOf (declBody p "sumTo__int")))

  , testCase "an uninstantiated polymorphic function is kept as it always was" $ do
      p <- typed "unused x = x + x\naddTwice x = x + x\nmain = (addTwice 1.0, addTwice 1)\n"
      assertBool "unused kept under its own name" ("unused" `elem` declNames p)

  , testCase "a mangled name never captures a user declaration" $ do
      p <- typed "addTwice__int = 7\naddTwice x = x + x\nmain = (addTwice 1.0, (addTwice 1, addTwice__int))\n"
      assertEqual "user declaration untouched" TInt (declType p "addTwice__int")
      assertBool "instance renamed around it" ("addTwice__int_" `elem` declNames p)
      assertEqual "main" (Tuple TFloat (Tuple TInt TInt)) (declType p "main")

  , testCase "the instances generate the right values" $ do
      p <- parse "add x y = x + y\nmain = (add 1.5 2.0, add 1 2)\n"
      case runGen defaultCompilerConfig p [] of
        Left e -> assertFailure ("compile failed: " ++ e)
        Right g -> assertEqual "sample" "VTuple (VFloat 3.5) (VInt 3)" (show (evalRand g (mkStdGen 1)))

  , testCase "a class constraint is still checked at each instance" $ do
      -- Reported at the use that instantiates it at Bool, in the user's
      -- vocabulary; the monomorphic-first fallback blamed the well-typed
      -- 'addTwice 1.0' ("Couldn't match type 'Float' with 'Bool'" at 2:32).
      msg <- typeError "addTwice x = x + x\nmain = (addTwice 1.0, addTwice True)\n"
      assertBool ("diagnostic names the instance: " ++ msg) ("No instance for (Num Bool)" `isInfixOf` msg)
      assertBool ("diagnostic names the use's position: " ++ msg) ("poly.ppl:2:23:" `isInfixOf` msg)
      assertBool ("solver internals leaked: " ++ msg) (not ("TV " `isInfixOf` msg) && not ("CNum" `isInfixOf` msg))

  , testCase "an ill-typed program is blamed at its type clash" $ do
      msg <- typeError "f x = x + 1.0\nmain = f True\n"
      assertBool ("diagnostic names the clash: " ++ msg) ("Couldn't match type" `isInfixOf` msg)
      assertBool ("diagnostic names Bool: " ++ msg) ("Bool" `isInfixOf` msg)

  , testCase "a helper used at two types is not blamed for an error elsewhere" $ do
      -- The monomorphic-first fallback reported its own error when the
      -- generalised retry failed too: 'addTwice 1' at 3:33, "Couldn't match
      -- type 'Float' with 'Int'", a well-typed use. The real mistake is
      -- 'f True'.
      msg <- typeError "addTwice x = x + x\nf x = x + 1.0\nmain = (addTwice 1.0, (addTwice 1, f True))\n"
      assertBool ("diagnostic names Bool: " ++ msg) ("Bool" `isInfixOf` msg)
      assertBool ("diagnostic blames line 3: " ++ msg) ("poly.ppl:3:" `isInfixOf` msg)
      assertBool ("the two-type use was blamed: " ++ msg) (not ("poly.ppl:3:33" `isInfixOf` msg))
      assertBool ("diagnostic mentions Int: " ++ msg) (not ("Int" `isInfixOf` msg))

  , testCase "a nullary declaration used at two types is cloned per type" $ do
      -- No monomorphism restriction (task rinfer-generalise-unconditionally):
      -- a declaration without parameters whose type is class-constrained is
      -- generalised like any other.
      p <- typed "twice = \\x -> x + x\nmain = (twice 1.0, twice 1)\n"
      assertEqual "declarations" (sort ["main", "twice__int", "twice__float"]) (sort (declNames p))
      assertEqual "Int instance" (TArrow TInt TInt) (declType p "twice__int")
      assertEqual "Float instance" (TArrow TFloat TFloat) (declType p "twice__float")
      assertEqual "main" (Tuple TFloat TInt) (declType p "main")

  , testCase "a random nullary declaration used at two types draws per use" $ do
      p <- typed "pick = if Uniform < 0.5 then (\\x -> x) else (\\x -> x + x)\nmain = (pick 1.0, pick 1)\n"
      assertEqual "declarations" (sort ["main", "pick__int", "pick__float"]) (sort (declNames p))
      src <- parse "pick = if Uniform < 0.5 then (\\x -> x) else (\\x -> x + x)\nmain = (pick 1.0, pick 1)\n"
      case runGen defaultCompilerConfig src [] of
        Left e -> assertFailure ("compile failed: " ++ e)
        Right g -> do
          let samples = [ show (evalRand g (mkStdGen seed)) | seed <- [1 .. 40] ]
          assertBool "every sample is one of the four combinations"
            (all (`elem` [ "VTuple (VFloat " ++ a ++ ") (VInt " ++ b ++ ")" | a <- ["1.0", "2.0"], b <- ["1", "2"] ]) samples)
          -- Each reference is its own draw: the two components disagree in
          -- some samples, which one shared draw would never do.
          assertBool ("the two uses never draw independently: " ++ show samples)
            (any (`elem` ["VTuple (VFloat 1.0) (VInt 2)", "VTuple (VFloat 2.0) (VInt 1)"]) samples)
  ]

parse :: String -> IO Program
parse src = either (\e -> assertFailure (show e) >> undefined) return (tryParseProgram "poly.ppl" src)

typed :: String -> IO Program
typed src = do
  p <- parse src
  either (\e -> assertFailure ("type inference failed: " ++ e) >> undefined) return (addRTypeInfo p)

typeError :: String -> IO String
typeError src = do
  p <- parse src
  either return (const (assertFailure "accepted an ill-typed program" >> return "")) (addRTypeInfo p)

declNames :: Program -> [String]
declNames = map fst . functions

declBody :: Program -> String -> Expr
declBody p n = maybe (error ("no declaration " ++ n)) id (lookup n (functions p))

declType :: Program -> String -> RType
declType p n = rType (ann (declBody p n))

varsOf :: Expr -> [String]
varsOf (Expr _ e) = own ++ concatMap varsOf (foldr (:) [] e)
  where own = case e of
          Var v -> [v]
          _ -> []
