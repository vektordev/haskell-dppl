module Main (main) where

import Test.Tasty (defaultMain)
import TestIRTypeCheck (irTypeCheckTests)

main :: IO ()
main = defaultMain irTypeCheckTests
