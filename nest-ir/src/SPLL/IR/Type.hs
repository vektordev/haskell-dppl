-- | The value types of the IR. Kept apart from "SPLL.IRTypeCheck" so that the IR's ADT functions
-- ("SPLL.IR.ADT") can state their types without importing the checker.
module SPLL.IR.Type
  ( IRType(..)
  , IRADTDecl(..)
  , IRADTConstructorDecl
  ) where
import SPLL.IR.Value (Shape)

-- | The value types of the IR.
--
-- Unlike 'RType', a tensor's element type is not restricted to a scalar: the
-- compiler builds 'BTensor's over enumerated domains of tuples, 'Either's and
-- ADT values (an enumerated sum maps over one). A tensor's shape is part of
-- its type, as in 'TTensor', and two tensor types unify only at equal shapes.
data IRType
  = ITBool
  | ITInt
  | ITFloat
  | ITSymbol
  | ITUnit
  | ITThetaTree
  | ITList IRType
  | ITTuple IRType IRType
  | ITEither IRType IRType
  | ITADT String          -- ^ By type name, as 'TADT'.
  | ITTensor Shape IRType
  | ITArrow IRType IRType
  | ITVar Int             -- ^ A type variable. In a checker result, a variable is universally quantified.
  deriving (Show, Eq, Ord)

-- | An algebraic data type as the IR knows it: constructors with typed fields.
data IRADTDecl = IRADTDecl
  { irDataName :: String
  , irConstructors :: [IRADTConstructorDecl]
  } deriving (Show, Eq)

type IRADTConstructorDecl = (String, [(String, IRType)])
