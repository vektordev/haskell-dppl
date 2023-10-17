{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE EmptyDataDeriving #-}

module SPLL.Typing.ResultTypes where

data ClassD deriving Show
data ClassI deriving Show
data ClassP deriving Show
data ClassB deriving Show

class SumResultType a b res | a b -> res
instance SumResultType ClassD ClassD ClassD
instance SumResultType ClassD ClassI ClassI
instance SumResultType ClassI ClassD ClassI
instance SumResultType ClassI ClassI ClassB
instance SumResultType ClassD ClassP ClassP
instance SumResultType ClassI ClassP ClassB
instance SumResultType ClassP ClassD ClassP
instance SumResultType ClassP ClassI ClassB
instance SumResultType ClassP ClassP ClassB
instance SumResultType a ClassB ClassB
instance SumResultType ClassB a ClassB

class CompResultType a b res | a b -> res
instance CompResultType ClassD ClassD ClassD
instance CompResultType ClassD ClassI ClassI
instance CompResultType ClassI ClassD ClassI
instance CompResultType ClassI ClassI ClassB
instance CompResultType ClassD ClassP ClassB
instance CompResultType ClassI ClassP ClassB
instance CompResultType ClassP ClassD ClassB
instance CompResultType ClassP ClassI ClassB
instance CompResultType ClassP ClassP ClassB
instance CompResultType a ClassB ClassB
instance CompResultType ClassB a ClassB

class DowngradeResultType a b res | a b -> res
instance DowngradeResultType ClassD ClassD ClassD
instance DowngradeResultType ClassD ClassI ClassI
instance DowngradeResultType ClassI ClassD ClassI
instance DowngradeResultType ClassI ClassI ClassI
instance DowngradeResultType ClassD ClassP ClassP
instance DowngradeResultType ClassI ClassP ClassP
instance DowngradeResultType ClassP ClassD ClassP
instance DowngradeResultType ClassP ClassI ClassP
instance DowngradeResultType ClassP ClassP ClassP
instance DowngradeResultType a ClassB ClassB
instance DowngradeResultType ClassB a ClassB