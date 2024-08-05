-- |
-- Module       : Data.Interval
-- Copyright    : (c) Melanie Brown 2023
-- License      : BSD3 (see the file LICENSE)
--
-- Intervals over types and their operations.
module Data.Interval (
  -- * The Interval type
  Interval,

  -- ** Construction

  -- *** Finite intervals
  pattern (:<>:),
  pattern (:<|:),
  pattern (:|>:),
  pattern (:||:),
  pattern (:--:),

  -- *** Possibly-infinite intervals

  -- |
  -- The first four form a @{-# COMPLETE #-}@ set of bidirectional patterns,
  -- and the final is a @{-# COMPLETE #-}@ unidirectional pattern on its own.
  pattern (:<->:),
  pattern (:<-|:),
  pattern (:|->:),
  pattern (:|-|:),
  pattern (:---:),

  -- *** Miscellaneous constructors
  pattern Whole,
  (+/-),
  (...),
  interval,
  point,

  -- ** Deconstruction
  bounds,
  lower,
  lowerBound,
  upper,
  upperBound,
  imin,
  iinf,
  isup,
  imax,

  -- ** Modification
  imap,
  imapLev,
  itraverse,
  itraverseLev,
  open,
  close,
  openclosed,
  closedopen,
  openLower,
  closedLower,
  openUpper,
  closedUpper,
  setLower,
  setUpper,

  -- * Computing with intervals
  Adjacency (..),
  hull,
  hulls,
  within,
  converseAdjacency,
  adjacency,
  intersect,
  union,
  unions,
  unionsAsc,
  complement,
  difference,
  (\\),
  symmetricDifference,
  measure,
  measuring,
  hausdorff,
  isSubsetOf,

  -- * Bounds
  Extremum (..),
  opposite,
  Bound (..),
  unBound,
  Bounding (..),
  compareBounds,
  SomeBound (..),
  unSomeBound,
  oppose,

  -- * Re-exports
  OneOrTwo (..),
) where

import Algebra.Lattice.Levitated (Levitated (..), foldLevitated)
import Control.Applicative (liftA2)
import Control.DeepSeq
import Control.Monad (join)
import Data.Data
import Data.Function (on)
import Data.Functor.Const (Const (Const))
import Data.Hashable (Hashable (..))
import Data.Kind (Constraint, Type)
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.OneOrTwo (OneOrTwo (..))
import Data.Ord (comparing)
import GHC.Generics (Generic (..), type (:*:) (..))

-- | The kinds of extremum an interval can have.
data Extremum
  = Minimum
  | Infimum
  | Supremum
  | Maximum
  deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic, Data, Typeable)

-- |
-- The 'opposite' of an 'Extremum' is its complementary analogue:
-- how the same point would be viewed from the complement of the
-- interval to which it belongs.
--
-- c.f. 'opposeBound'.
opposite :: Extremum -> Extremum
opposite = \case
  Minimum -> Supremum
  Infimum -> Maximum
  Supremum -> Minimum
  Maximum -> Infimum

-- | A 'Bound' is an endpoint of an 'Interval'.
type Bound :: Extremum -> Type -> Type
data Bound ext x where
  Min :: !x -> Bound Minimum x
  Inf :: !x -> Bound Infimum x
  Sup :: !x -> Bound Supremum x
  Max :: !x -> Bound Maximum x

-- | Extract the term from a 'Bound'.
unBound :: Bound ext x -> x
unBound = \case
  Min x -> x
  Inf x -> x
  Sup x -> x
  Max x -> x

instance Functor (Bound ext) where
  fmap :: (a -> b) -> Bound ext a -> Bound ext b
  fmap f = \case
    Min x -> Min (f x)
    Inf x -> Inf (f x)
    Sup x -> Sup (f x)
    Max x -> Max (f x)

instance Foldable (Bound ext) where
  foldMap :: (Monoid m) => (a -> m) -> Bound ext a -> m
  foldMap f = \case
    Min x -> f x
    Inf x -> f x
    Sup x -> f x
    Max x -> f x

instance Traversable (Bound ext) where
  traverse :: (Applicative f) => (a -> f b) -> Bound ext a -> f (Bound ext b)
  traverse f = \case
    Min x -> Min <$> f x
    Inf x -> Inf <$> f x
    Sup x -> Sup <$> f x
    Max x -> Max <$> f x

instance (Eq x) => Eq (Bound ext x) where
  (==) :: (Eq x) => Bound ext x -> Bound ext x -> Bool
  Min x == Min y = x == y
  Inf x == Inf y = x == y
  Sup x == Sup y = x == y
  Max x == Max y = x == y

instance (Ord x) => Ord (Bound ext (Levitated x)) where
  compare ::
    (Ord x) => Bound ext (Levitated x) -> Bound ext (Levitated x) -> Ordering
  compare = compareBounds

-- | A type class for inverting 'Bound's.
type Bounding :: Extremum -> Constraint
class (Opposite (Opposite ext) ~ ext) => Bounding ext where
  type Opposite ext :: Extremum

  bound :: x -> Bound ext x

  -- | c.f. 'opposite'.
  opposeBound :: Bound ext x -> Bound (Opposite ext) x

instance Bounding Minimum where
  type Opposite Minimum = Supremum

  bound :: x -> Bound Minimum x
  bound = Min

  opposeBound :: Bound Minimum x -> Bound Supremum x
  opposeBound (Min x) = Sup x

instance Bounding Infimum where
  type Opposite Infimum = Maximum

  bound :: x -> Bound Infimum x
  bound = Inf

  opposeBound :: Bound Infimum x -> Bound Maximum x
  opposeBound (Inf x) = Max x

instance Bounding Supremum where
  type Opposite Supremum = Minimum

  bound :: x -> Bound Supremum x
  bound = Sup

  opposeBound :: Bound Supremum x -> Bound Minimum x
  opposeBound (Sup x) = Min x

instance Bounding Maximum where
  type Opposite Maximum = Infimum

  bound :: x -> Bound Maximum x
  bound = Max

  opposeBound :: Bound Maximum x -> Bound Infimum x
  opposeBound (Max x) = Inf x

-- | 'Bound's have special comparison rules for identical points.
--
-- >>> compareBounds (Min (Levitate 0)) (Max (Levitate 0))
-- EQ
-- >>> compareBounds (Inf (Levitate 0)) (Sup (Levitate 0))
-- GT
-- >>> compareBounds (Max (Levitate 0)) (Sup (Levitate 0))
-- GT
-- >>> compareBounds (Inf (Levitate 0)) (Min (Levitate 0))
-- GT
-- >>> compareBounds (Max (Levitate 0)) (Inf (Levitate 0))
-- LT
compareBounds ::
  (Ord x) =>
  Bound ext1 x ->
  Bound ext2 x ->
  Ordering
compareBounds (Min l) = \case
  Min ll -> compare l ll
  Inf ll -> compare l ll <> LT
  Sup u -> compare l u <> GT
  Max u -> compare l u
compareBounds (Inf l) = \case
  Min ll -> compare l ll <> GT
  Inf ll -> compare l ll
  Sup u -> compare l u <> GT
  Max u -> compare l u <> GT
compareBounds (Sup l) = \case
  Min u -> compare l u <> LT
  Inf u -> compare l u <> LT
  Sup uu -> compare l uu
  Max uu -> compare l uu <> LT
compareBounds (Max l) = \case
  Min u -> compare l u
  Inf u -> compare l u <> LT
  Sup uu -> compare l uu <> GT
  Max uu -> compare l uu

data SomeBound x
  = forall ext.
    (Bounding ext, Bounding (Opposite ext)) =>
    SomeBound !(Bound ext x)

instance (Eq x) => Eq (SomeBound (Levitated x)) where
  (==) :: (Eq x) => SomeBound (Levitated x) -> SomeBound (Levitated x) -> Bool
  SomeBound (Min a) == SomeBound (Min b) = a == b
  SomeBound (Max a) == SomeBound (Max b) = a == b
  SomeBound (Inf a) == SomeBound (Inf b) = a == b
  SomeBound (Sup a) == SomeBound (Sup b) = a == b
  _ == _ = False

instance (Ord x) => Ord (SomeBound (Levitated x)) where
  compare ::
    (Ord x) => SomeBound (Levitated x) -> SomeBound (Levitated x) -> Ordering
  SomeBound b0 `compare` SomeBound b1 = compareBounds b0 b1

oppose :: SomeBound x -> SomeBound x
oppose (SomeBound b) = SomeBound (opposeBound b)

unSomeBound :: (Ord x) => SomeBound x -> x
unSomeBound (SomeBound b) = unBound b

infix 5 :<-->:

infix 5 :<--|:

infix 5 :|-->:

infix 5 :|--|:

type Interval :: Type -> Type
data Interval x where
  -- | Open-open interval. You probably want '(:<->:)' or '(:<>:)'.
  (:<-->:) ::
    (Ord x) =>
    !(Bound Infimum (Levitated x)) ->
    !(Bound Supremum (Levitated x)) ->
    Interval x
  -- | Open-closed interval. You probably want '(:<-|:)' or '(:<|:)'.
  (:<--|:) ::
    (Ord x) =>
    !(Bound Infimum (Levitated x)) ->
    !(Bound Maximum (Levitated x)) ->
    Interval x
  -- | Closed-open interval. You probably want '(:|->:)' or '(:|>:)'.
  (:|-->:) ::
    (Ord x) =>
    !(Bound Minimum (Levitated x)) ->
    !(Bound Supremum (Levitated x)) ->
    Interval x
  -- | Closed-closed interval. You probably want '(:|-|:)' or '(:||:)'.
  (:|--|:) ::
    (Ord x) =>
    !(Bound Minimum (Levitated x)) ->
    !(Bound Maximum (Levitated x)) ->
    Interval x

infix 5 :<->:

infix 5 :<-|:

infix 5 :|->:

infix 5 :|-|:

-- | A bidirectional pattern synonym matching open intervals.
pattern (:<->:) :: (Ord x) => Levitated x -> Levitated x -> Interval x
pattern l :<->: u <-
  Inf l :<-->: Sup u
  where
    b1 :<->: b2 =
      let inf = min b1 b2
          sup = max b1 b2
       in case compare b1 b2 of
            EQ -> Min inf :|--|: Max sup
            _ -> Inf inf :<-->: Sup sup

-- | A bidirectional pattern synonym matching open-closed intervals.
pattern (:<-|:) :: (Ord x) => Levitated x -> Levitated x -> Interval x
pattern l :<-|: u <-
  Inf l :<--|: Max u
  where
    b1 :<-|: b2 =
      let inf = min b1 b2
          sup = max b1 b2
       in case compare b1 b2 of
            LT -> Inf inf :<--|: Max sup
            EQ -> Min inf :|--|: Max sup
            GT -> Min inf :|-->: Sup sup

-- | A bidirectional pattern synonym matching closed-open intervals.
pattern (:|->:) :: (Ord x) => Levitated x -> Levitated x -> Interval x
pattern l :|->: u <-
  Min l :|-->: Sup u
  where
    b1 :|->: b2 =
      let inf = min b1 b2
          sup = max b1 b2
       in case compare b1 b2 of
            LT -> Min inf :|-->: Sup sup
            EQ -> Min inf :|--|: Max sup
            GT -> Inf inf :<--|: Max sup

-- | A bidirectional pattern synonym matching closed intervals.
pattern (:|-|:) :: (Ord x) => Levitated x -> Levitated x -> Interval x
pattern l :|-|: u <-
  Min l :|--|: Max u
  where
    b1 :|-|: b2 = Min (min b1 b2) :|--|: Max (max b1 b2)

{-# COMPLETE (:<->:), (:<-|:), (:|->:), (:|-|:) #-}

-- | A unidirectional pattern synonym ignoring the particular 'Bound's.
pattern (:---:) :: forall x. (Ord x) => Levitated x -> Levitated x -> Interval x
pattern l :---: u <-
  (bounds -> (SomeBound (unBound -> l), SomeBound (unBound -> u)))

{-# COMPLETE (:---:) #-}

infix 5 :<>:

infix 5 :<|:

infix 5 :|>:

infix 5 :||:

-- | A bidirectional pattern synonym matching finite open intervals.
pattern (:<>:) :: forall x. (Ord x) => x -> x -> Interval x
pattern l :<>: u <-
  Levitate l :<->: Levitate u
  where
    b1 :<>: b2 =
      let inf = Levitate (min b1 b2)
          sup = Levitate (max b1 b2)
       in case compare b1 b2 of
            EQ -> Min inf :|--|: Max sup
            _ -> Inf inf :<-->: Sup sup

-- | A bidirectional pattern synonym matching finite open-closed intervals.
pattern (:<|:) :: forall x. (Ord x) => x -> x -> Interval x
pattern l :<|: u <-
  Levitate l :<-|: Levitate u
  where
    b1 :<|: b2 =
      let inf = Levitate (min b1 b2)
          sup = Levitate (max b1 b2)
       in case compare b1 b2 of
            LT -> Inf inf :<--|: Max sup
            EQ -> Min inf :|--|: Max sup
            GT -> Min inf :|-->: Sup sup

-- | A bidirectional pattern synonym matching finite closed-open intervals.
pattern (:|>:) :: forall x. (Ord x) => x -> x -> Interval x
pattern l :|>: u <-
  Levitate l :|->: Levitate u
  where
    b1 :|>: b2 =
      let inf = Levitate (min b1 b2)
          sup = Levitate (max b1 b2)
       in case compare b1 b2 of
            LT -> Min inf :|-->: Sup sup
            EQ -> Min inf :|--|: Max sup
            GT -> Inf inf :<--|: Max sup

-- | A bidirectional pattern synonym matching finite closed intervals.
pattern (:||:) :: forall x. (Ord x) => x -> x -> Interval x
pattern l :||: u <-
  Levitate l :|-|: Levitate u
  where
    b1 :||: b2 = Min (Levitate $ min b1 b2) :|--|: Max (Levitate $ max b1 b2)

-- |
-- A unidirectional pattern synonym matching finite intervals,
-- that ignores the particular 'Bound's.
pattern (:--:) :: forall x. (Ord x) => x -> x -> Interval x
pattern l :--: u <-
  ( bounds ->
      (SomeBound (unBound -> Levitate l), SomeBound (unBound -> Levitate u))
    )

-- | The whole interval, 'Bottom' ':|-|:' 'Top'.
pattern Whole :: (Ord x) => Interval x
pattern Whole = Bottom :|-|: Top

deriving instance (Ord x) => Eq (Interval x)

instance (Ord x, Show x) => Show (Interval x) where
  show :: (Ord x, Show x) => Interval x -> String
  show = \case
    l :<>: u -> "(" <> show l <> " :<>: " <> show u <> ")"
    l :|>: u -> "(" <> show l <> " :|>: " <> show u <> ")"
    l :<|: u -> "(" <> show l <> " :<|: " <> show u <> ")"
    l :||: u -> "(" <> show l <> " :||: " <> show u <> ")"
    l :<->: u -> "(" <> show l <> " :<->: " <> show u <> ")"
    l :|->: u -> "(" <> show l <> " :|->: " <> show u <> ")"
    l :<-|: u -> "(" <> show l <> " :<-|: " <> show u <> ")"
    l :|-|: u -> "(" <> show l <> " :|-|: " <> show u <> ")"

instance (Ord x) => Ord (Interval x) where
  compare :: (Ord x) => Interval x -> Interval x -> Ordering
  compare i1 i2 = on compare lower i1 i2 <> on compare upper i1 i2

instance (Ord x, Data x) => Data (Interval x) where
  gfoldl ::
    (Ord x, Data x) =>
    (forall d b. (Data d) => c (d -> b) -> d -> c b) ->
    (forall g. g -> c g) ->
    Interval x ->
    c (Interval x)
  gfoldl (<^>) gpure = \case
    l :<->: u -> gpure (:<->:) <^> l <^> u
    l :|->: u -> gpure (:|->:) <^> l <^> u
    l :<-|: u -> gpure (:<-|:) <^> l <^> u
    l :|-|: u -> gpure (:|-|:) <^> l <^> u

  toConstr :: (Ord x, Data x) => Interval x -> Constr
  toConstr = \case
    _ :<->: _ -> intervalOpenOpenConstr
    _ :|->: _ -> intervalClosedOpenConstr
    _ :<-|: _ -> intervalOpenClosedConstr
    _ :|-|: _ -> intervalClosedClosedConstr

  dataTypeOf :: (Ord x, Data x) => Interval x -> DataType
  dataTypeOf _ = intervalDataType

  gunfold ::
    (Ord x, Data x) =>
    (forall b r. (Data b) => c (b -> r) -> c r) ->
    (forall r. r -> c r) ->
    Constr ->
    c (Interval x)
  gunfold k gpure constr = case constrIndex constr of
    0 -> k (k (gpure (:<->:)))
    1 -> k (k (gpure (:|->:)))
    2 -> k (k (gpure (:<-|:)))
    3 -> k (k (gpure (:|-|:)))
    _ -> error "gunfold"

intervalOpenOpenConstr :: Constr
intervalOpenOpenConstr =
  mkConstr
    intervalDataType
    ":<-->:"
    []
    Infix

intervalClosedOpenConstr :: Constr
intervalClosedOpenConstr =
  mkConstr
    intervalDataType
    ":|-->:"
    []
    Infix

intervalOpenClosedConstr :: Constr
intervalOpenClosedConstr =
  mkConstr
    intervalDataType
    ":<--|:"
    []
    Infix

intervalClosedClosedConstr :: Constr
intervalClosedClosedConstr =
  mkConstr
    intervalDataType
    ":|--|:"
    []
    Infix

intervalDataType :: DataType
intervalDataType =
  mkDataType
    "Data.Interval.Interval"
    [ intervalOpenOpenConstr
    , intervalClosedOpenConstr
    , intervalOpenClosedConstr
    , intervalClosedClosedConstr
    ]

deriving instance (Typeable x) => Typeable (Interval x)

instance (Ord x, Generic x) => Generic (Interval x) where
  type
    Rep (Interval x) =
      (Const (Levitated x, Extremum) :*: Const (Levitated x, Extremum))

  from :: (Ord x, Generic x) => Interval x -> Rep (Interval x) x1
  from = \case
    l :<->: u -> (Const (l, Infimum) :*: Const (u, Supremum))
    l :|->: u -> (Const (l, Minimum) :*: Const (u, Supremum))
    l :<-|: u -> (Const (l, Infimum) :*: Const (u, Maximum))
    l :|-|: u -> (Const (l, Minimum) :*: Const (u, Maximum))

  to :: (Ord x, Generic x) => Rep (Interval x) x1 -> Interval x
  to (Const l :*: Const u) = l ... u

instance (Ord x, Hashable x) => Hashable (Interval x) where
  hashWithSalt :: (Ord x, Hashable x) => Int -> Interval x -> Int
  hashWithSalt s = \case
    l :<->: u -> s `hashWithSalt` (1 :: Int) `hashWithSalt` l `hashWithSalt` u
    l :|->: u -> s `hashWithSalt` (2 :: Int) `hashWithSalt` l `hashWithSalt` u
    l :<-|: u -> s `hashWithSalt` (3 :: Int) `hashWithSalt` l `hashWithSalt` u
    l :|-|: u -> s `hashWithSalt` (4 :: Int) `hashWithSalt` l `hashWithSalt` u

instance (Ord x, NFData x) => NFData (Interval x) where
  rnf :: (Ord x, NFData x) => Interval x -> ()
  rnf (x :---: y) = x `seq` y `seq` ()

-- | Since the 'Ord' constraints on the constructors for 'Interval'
-- prevent it from being a 'Functor', this will have to suffice.
imap :: (Ord x, Ord y) => (x -> y) -> Interval x -> Interval y
imap f = \case
  l :<->: u -> fmap f l :<->: fmap f u
  l :|->: u -> fmap f l :|->: fmap f u
  l :<-|: u -> fmap f l :<-|: fmap f u
  l :|-|: u -> fmap f l :|-|: fmap f u

-- | Same as 'imap' but on the 'Levitated' of the underlying type.
imapLev ::
  (Ord x, Ord y) =>
  (Levitated x -> Levitated y) ->
  Interval x ->
  Interval y
imapLev f = \case
  l :<->: u -> f l :<->: f u
  l :|->: u -> f l :|->: f u
  l :<-|: u -> f l :<-|: f u
  l :|-|: u -> f l :|-|: f u

-- | Since the 'Ord' constraints on the constructors for 'Interval'
-- prevent it from being 'Traversable', this will have to suffice.
itraverse ::
  (Ord x, Ord y, Applicative f) =>
  (x -> f y) ->
  Interval x ->
  f (Interval y)
itraverse f = \case
  l :<->: u -> liftA2 (:<->:) (traverse f l) (traverse f u)
  l :|->: u -> liftA2 (:|->:) (traverse f l) (traverse f u)
  l :<-|: u -> liftA2 (:<-|:) (traverse f l) (traverse f u)
  l :|-|: u -> liftA2 (:|-|:) (traverse f l) (traverse f u)

-- | Same as 'itraverse' but on the 'Levitated' of the underlying type.
itraverseLev ::
  (Ord x, Ord y, Applicative f) =>
  (Levitated x -> f (Levitated y)) ->
  Interval x ->
  f (Interval y)
itraverseLev f = \case
  l :<->: u -> liftA2 (:<->:) (f l) (f u)
  l :|->: u -> liftA2 (:|->:) (f l) (f u)
  l :<-|: u -> liftA2 (:<-|:) (f l) (f u)
  l :|-|: u -> liftA2 (:|-|:) (f l) (f u)

-- | Get the @('lower', 'upper')@ bounds of an 'Interval'.
bounds :: Interval x -> (SomeBound (Levitated x), SomeBound (Levitated x))
bounds = \case
  l :<-->: u -> (SomeBound l, SomeBound u)
  l :<--|: u -> (SomeBound l, SomeBound u)
  l :|-->: u -> (SomeBound l, SomeBound u)
  l :|--|: u -> (SomeBound l, SomeBound u)

-- | Get the lower bound of an interval.
--
-- > lower = fst . bounds
lower :: (Ord x) => Interval x -> SomeBound (Levitated x)
lower = fst . bounds

-- | Get the upper bound of an interval.
--
-- > upper = snd . bounds
upper :: (Ord x) => Interval x -> SomeBound (Levitated x)
upper = snd . bounds

-- | Get the lower bound of an interval
-- (with the bound expressed at the term level).
lowerBound :: (Ord x) => Interval x -> (Levitated x, Extremum)
lowerBound = \case
  l :<->: _ -> (l, Infimum)
  l :<-|: _ -> (l, Infimum)
  l :|->: _ -> (l, Minimum)
  l :|-|: _ -> (l, Minimum)

-- | Get the upper bound of an interval
-- (with the bound expressed at the term level).
upperBound :: (Ord x) => Interval x -> (Levitated x, Extremum)
upperBound = \case
  _ :<->: u -> (u, Supremum)
  _ :<-|: u -> (u, Maximum)
  _ :|->: u -> (u, Supremum)
  _ :|-|: u -> (u, Maximum)

-- | Given 'SomeBound's, try to make an interval.
interval ::
  (Ord x) =>
  SomeBound (Levitated x) ->
  SomeBound (Levitated x) ->
  Interval x
interval (SomeBound b1) (SomeBound b2) = case (b1, b2) of
  (Min l, Sup u) -> l :|->: u
  (Min l, Max u) -> l :|-|: u
  (Inf l, Sup u) -> l :<->: u
  (Inf l, Max u) -> l :<-|: u
  (Sup u, Min l) -> l :|->: u
  (Sup u, Inf l) -> l :<->: u
  (Max u, Min l) -> l :|-|: u
  (Max u, Inf l) -> l :<-|: u
  _ -> error "cannot make an interval with the given bounds"

-- | Given limits and 'Extremum's, try to make an interval.
(...) ::
  (Ord x) =>
  (Levitated x, Extremum) ->
  (Levitated x, Extremum) ->
  Interval x
(x, b1) ... (y, b2) = case (b1, b2) of
  (Minimum, Supremum) -> l :|->: u
  (Minimum, Maximum) -> l :|-|: u
  (Infimum, Supremum) -> l :<->: u
  (Infimum, Maximum) -> l :<-|: u
  (Supremum, Minimum) -> l :|->: u
  (Supremum, Infimum) -> l :<->: u
  (Maximum, Minimum) -> l :|-|: u
  (Maximum, Infimum) -> l :<-|: u
  _ -> error "cannot make an interval with the given bounds"
 where
  l = min x y
  u = max x y

-- | According to
-- [Allen](https://en.wikipedia.org/wiki/Allen%27s_interval_algebra),
-- two intervals can be "adjacent" in 13 different ways,
-- into at most 3 distinct intervals. In this package,
-- this quality is called the 'Adjacency' of the intervals.
data Adjacency x
  = Before !(Interval x) !(Interval x)
  | Meets !(Interval x) !(Interval x) !(Interval x)
  | Overlaps !(Interval x) !(Interval x) !(Interval x)
  | Starts !(Interval x) !(Interval x)
  | During !(Interval x) !(Interval x) !(Interval x)
  | Finishes !(Interval x) !(Interval x)
  | Identical !(Interval x)
  | FinishedBy !(Interval x) !(Interval x)
  | Contains !(Interval x) !(Interval x) !(Interval x)
  | StartedBy !(Interval x) !(Interval x)
  | OverlappedBy !(Interval x) !(Interval x) !(Interval x)
  | MetBy !(Interval x) !(Interval x) !(Interval x)
  | After !(Interval x) !(Interval x)
  deriving (Eq, Ord, Show, Generic, Typeable, Data)

-- | The result of having compared the same two intervals in reverse order.
converseAdjacency :: Adjacency x -> Adjacency x
converseAdjacency = \case
  Before i j -> After i j
  Meets i j k -> MetBy i j k
  Overlaps i j k -> OverlappedBy i j k
  Starts i j -> StartedBy i j
  During i j k -> Contains i j k
  Finishes i j -> FinishedBy i j
  Identical i -> Identical i
  FinishedBy i j -> Finishes i j
  Contains i j k -> During i j k
  StartedBy i j -> Starts i j
  OverlappedBy i j k -> Overlaps i j k
  MetBy i j k -> Meets i j k
  After i j -> Before i j

-- | Calculate the 'Adjacency' between two intervals, according to
-- [Allen](https://en.wikipedia.org/wiki/Allen%27s_interval_algebra).
adjacency :: (Ord x) => Interval x -> Interval x -> Adjacency x
adjacency i1 i2 = case (comparing lower i1 i2, comparing upper i1 i2) of
  (LT, LT) -> case unSomeBound ub1 `compare` unSomeBound lb2 of
    LT -> Before i1 i2
    EQ -> case (ub1, lb2) of
      (SomeBound (Max _), SomeBound (Min _)) ->
        Meets
          (openUpper i1)
          (interval lb2 ub1)
          (openLower i2)
      _ -> Before i1 i2
    GT ->
      Overlaps
        (interval lb1 (oppose lb2))
        (interval lb2 ub1)
        (interval (oppose ub1) ub2)
  (LT, EQ) ->
    Finishes
      (interval lb1 (oppose lb2))
      i2
  (LT, GT) ->
    Contains
      (interval lb1 (oppose lb2))
      (interval lb2 ub2)
      (interval (oppose ub2) ub1)
  (EQ, LT) ->
    Starts
      i1
      (interval (oppose ub1) ub2)
  (EQ, EQ) -> Identical i1
  (EQ, GT) ->
    StartedBy
      i2
      (interval (oppose ub2) ub1)
  (GT, LT) ->
    During
      (interval lb2 (oppose lb1))
      (interval lb1 ub1)
      (interval (oppose ub1) ub2)
  (GT, EQ) ->
    FinishedBy
      (interval lb2 (oppose lb1))
      i1
  (GT, GT) -> case unSomeBound ub2 `compare` unSomeBound lb1 of
    GT ->
      OverlappedBy
        (interval lb2 (oppose lb1))
        (interval lb1 ub2)
        (interval (oppose ub2) ub1)
    EQ -> case (ub2, lb1) of
      (SomeBound (Max _), SomeBound (Min _)) ->
        MetBy
          (openUpper i2)
          (interval lb1 ub2)
          (openLower i1)
      _ -> After i2 i1
    LT -> After i2 i1
 where
  (lb1, ub1) = bounds i1
  (lb2, ub2) = bounds i2

-- | Get the convex hull of two intervals.
--
-- >>> hull (7 :|>: 8) (3 :|>: 4)
-- (3 :|>: 8)
--
-- >>> hull (Bottom :<-|: Levitate 3) (4 :<>: 5)
-- (Bottom :<->: Levitate 5)
hull :: (Ord x) => Interval x -> Interval x -> Interval x
hull i1 i2 = case adjacency i1 i2 of
  Before i j -> interval (lower i) (upper j)
  Meets i _ k -> interval (lower i) (upper k)
  Overlaps i _ k -> interval (lower i) (upper k)
  Starts i j -> interval (lower i) (upper j)
  During i _ k -> interval (lower i) (upper k)
  Finishes i j -> interval (lower i) (upper j)
  Identical i -> i
  FinishedBy i j -> interval (lower i) (upper j)
  Contains i _ k -> interval (lower i) (upper k)
  StartedBy i j -> interval (lower i) (upper j)
  OverlappedBy i _ k -> interval (lower i) (upper k)
  MetBy i _ k -> interval (lower i) (upper k)
  After i j -> interval (lower i) (upper j)

-- | Get the convex hull of a non-empty list of intervals.
hulls :: (Ord x) => NonEmpty (Interval x) -> Interval x
hulls (i :| []) = i
hulls (i :| j : is) = hulls (hull i j :| is)

-- | Test whether a point is contained in the interval.
within :: (Ord x) => Levitated x -> Interval x -> Bool
within x = \case
  l :<->: u -> l < x && x < u
  l :<-|: u -> l < x && x <= u
  l :|->: u -> l <= x && x < u
  l :|-|: u -> l <= x && x <= u

-- | Create the closed-closed interval at a given point.
point :: (Ord x) => x -> Interval x
point = join (:||:)

-- | Get the infimum of an interval, weakening if necessary.
iinf :: (Ord x) => Interval x -> Levitated x
iinf (x :---: _) = x

-- | Get the minimum of an interval, if it exists.
imin :: (Ord x) => Interval x -> Maybe (Levitated x)
imin = \case
  (x :|->: _) -> Just x
  (x :|-|: _) -> Just x
  _ -> Nothing

-- | Get the maximum of an interval, if it exists.
imax :: (Ord x) => Interval x -> Maybe (Levitated x)
imax = \case
  (_ :<-|: x) -> Just x
  (_ :|-|: x) -> Just x
  _ -> Nothing

-- | Get the supremum of an interval, weakening if necessary.
isup :: (Ord x) => Interval x -> Levitated x
isup (_ :---: x) = x

-- | Open both bounds of the given interval.
open :: (Ord x) => Interval x -> Interval x
open (l :---: u) = l :<->: u

-- | Close both bounds of the given interval.
close :: (Ord x) => Interval x -> Interval x
close (l :---: u) = l :|-|: u

-- | Make the interval open-closed, leaving the endpoints unchanged.
openclosed :: (Ord x) => Interval x -> Interval x
openclosed (l :---: u) = l :<-|: u

-- | Make the interval closed-open, leaving the endpoints unchanged.
closedopen :: (Ord x) => Interval x -> Interval x
closedopen (l :---: u) = l :|->: u

-- | Make the lower bound open, leaving the endpoints unchanged.
openLower :: (Ord x) => Interval x -> Interval x
openLower = \case
  l :<->: u -> l :<->: u
  l :<-|: u -> l :<-|: u
  l :|->: u -> l :<->: u
  l :|-|: u -> l :<-|: u

-- | Make the lower bound closed, leaving the endpoints unchanged.
closedLower :: (Ord x) => Interval x -> Interval x
closedLower = \case
  l :<->: u -> l :|->: u
  l :<-|: u -> l :|-|: u
  l :|->: u -> l :|->: u
  l :|-|: u -> l :|-|: u

-- | Make the upper bound open, leaving the endpoints unchanged.
openUpper :: (Ord x) => Interval x -> Interval x
openUpper = \case
  l :<->: u -> l :<->: u
  l :<-|: u -> l :<->: u
  l :|->: u -> l :|->: u
  l :|-|: u -> l :|->: u

-- | Make the upper bound closed, leaving the endpoints unchanged.
closedUpper :: (Ord x) => Interval x -> Interval x
closedUpper = \case
  l :<->: u -> l :<-|: u
  l :<-|: u -> l :<-|: u
  l :|->: u -> l :|-|: u
  l :|-|: u -> l :|-|: u

setLower :: (Ord x) => Levitated x -> Interval x -> Interval x
setLower x = \case
  _ :<->: u -> x :<->: u
  _ :<-|: u -> x :<-|: u
  _ :|->: u -> x :|->: u
  _ :|-|: u -> x :|-|: u

setUpper :: (Ord x) => Levitated x -> Interval x -> Interval x
setUpper x = \case
  l :<->: _ -> l :<->: x
  l :<-|: _ -> l :<-|: x
  l :|->: _ -> l :|->: x
  l :|-|: _ -> l :|-|: x

infixl 4 `intersect`

-- | Calculate the intersection of two intervals, if it exists.
--
-- @
-- >>> intersect (2 :<>: 4) (3 :||: 5)
-- Just (3 :|>: 4)
--
-- >>> intersect (2 :<>: 4) (4 :||: 5)
-- Nothing
--
-- >>> intersect (1 :<>: 4) (2 :||: 3)
-- Just (2 :||: 3)
-- @
intersect ::
  forall x.
  (Ord x) =>
  Interval x ->
  Interval x ->
  Maybe (Interval x)
intersect i1 i2 = case adjacency i1 i2 of
  Before _ _ -> Nothing
  Meets _ j _ -> Just j
  Overlaps _ j _ -> Just j
  Starts i _ -> Just i
  During _ j _ -> Just j
  Finishes _ j -> Just j
  Identical i -> Just i
  FinishedBy _ j -> Just j
  Contains _ j _ -> Just j
  StartedBy i _ -> Just i
  OverlappedBy _ j _ -> Just j
  MetBy _ j _ -> Just j
  After _ _ -> Nothing

infixl 4 `union`

-- | Get the union of two intervals, as either 'OneOrTwo'.
--
-- @
-- >>> union (2 :||: 5) (5 :<>: 7)
-- One (2 :|>: 7)
--
-- >>> union (2 :||: 4) (5 :<>: 7)
-- Two (2 :||: 4) (5 :<>: 7)
-- @
union ::
  forall x.
  (Ord x) =>
  Interval x ->
  Interval x ->
  OneOrTwo (Interval x)
union i1 i2 = case adjacency i1 i2 of
  Before i j
    | fst (upperBound i) == fst (lowerBound j) -> One (hull i j)
    | otherwise -> Two i j
  Meets i _ k -> One (hull i k)
  Overlaps i _ k -> One (hull i k)
  Starts i j -> One (hull i j)
  During i _ k -> One (hull i k)
  Finishes i j -> One (hull i j)
  Identical i -> One i
  FinishedBy i j -> One (hull i j)
  Contains i _ k -> One (hull i k)
  StartedBy i j -> One (hull i j)
  OverlappedBy i _ k -> One (hull i k)
  MetBy i _ k -> One (hull i k)
  After i j
    | fst (upperBound i) == fst (lowerBound j) -> One (hull i j)
    | otherwise -> Two i j

-- | /O(n log n)/. Get the union of a list of intervals.
--
-- This function uses 'sort'. See also 'unionsAsc'.
unions :: forall x. (Ord x) => [Interval x] -> [Interval x]
unions = unionsAsc . sort

-- | /O(n)/. Get the union of a sorted list of intervals.
--
-- NOTE: The input condition is not checked. Use with care.
unionsAsc :: forall x. (Ord x) => [Interval x] -> [Interval x]
unionsAsc = \case
  i : j : is -> case i `union` j of
    One k -> unionsAsc (k : is)
    _ -> i : unionsAsc (j : is)
  x -> x

-- | Take the complement of the interval, as possibly 'OneOrTwo'. See also 'Data.Interval.Borel.complement'.
--
-- @
-- >>> complement (3 :<>: 4)
-- Just (Two (Bottom :|-|: Levitate 3) (Levitate 4 :|-|: Top))
-- @
--
-- Note that infinitely-open intervals will include in their result
-- the points at infinity toward which they are infinite:
-- @
-- >>> complement (Levitate 3 :<->: Top)
-- Just (Two (Bottom :|-|: Levitate 3) (Top :|-|: Top))
-- @
complement ::
  forall x.
  (Ord x) =>
  Interval x ->
  Maybe (OneOrTwo (Interval x))
complement = \case
  Whole -> Nothing
  Bottom :|-|: u -> Just (One (u :<-|: Top))
  Bottom :|->: u -> Just (One (u :|-|: Top))
  Bottom :<-|: u -> Just (Two (Bottom :|-|: Bottom) (u :<-|: Top))
  Bottom :<->: u -> Just (Two (Bottom :|-|: Bottom) (u :|-|: Top))
  --
  l :|-|: Top -> Just (One (Bottom :|->: l))
  l :<-|: Top -> Just (One (Bottom :|-|: l))
  l :|->: Top -> Just (Two (Bottom :|->: l) (Top :|-|: Top))
  l :<->: Top -> Just (Two (Bottom :|-|: l) (Top :|-|: Top))
  --
  l :|-|: u -> Just (Two (Bottom :|->: l) (u :<-|: Top))
  l :|->: u -> Just (Two (Bottom :|->: l) (u :|-|: Top))
  l :<-|: u -> Just (Two (Bottom :|-|: l) (u :<-|: Top))
  l :<->: u -> Just (Two (Bottom :|-|: l) (u :|-|: Top))

infix 4 `difference`

-- | Remove all points of the second interval from the first.
--
-- @
-- >>> difference Whole (3 :<>: 4)
-- Just (Two (Bottom :|-|: Levitate 3) (Levitate 4 :|-|: Top))
--
-- >>> difference (1 :<>: 4) (2 :||: 5)
-- Just (One (1 :<>: 2))
--
-- >>> difference (1 :|>: 4) (0 :||: 1)
-- Just (One (1 :<>: 4))
--
-- >>> difference (1 :<>: 4) (0 :||: 1)
-- Just (One (1 :<>: 4))
-- @
difference ::
  forall x.
  (Ord x) =>
  Interval x ->
  Interval x ->
  Maybe (OneOrTwo (Interval x))
difference i1 i2 = case adjacency i1 i2 of
  -- not commutative!!
  Before i _ -> Just $ One i
  Meets i _ _ -> Just $ One i
  Overlaps i _ _ -> Just $ One i
  Starts{} -> Nothing
  During{} -> Nothing
  Finishes i _ -> Just $ One i
  Identical{} -> Nothing
  FinishedBy{} -> Nothing
  Contains i _ k -> Just $ Two i k
  StartedBy _ j -> Just $ One j
  OverlappedBy _ _ k -> Just $ One k
  MetBy _ _ k -> Just $ One k
  After _ j -> Just $ One j

-- | Infix synonym for 'difference'
(\\) ::
  forall x.
  (Ord x) =>
  Interval x ->
  Interval x ->
  Maybe (OneOrTwo (Interval x))
(\\) = difference

-- | The difference of the union and intersection of two intervals.
--
-- @
-- >>> symmetricDifference Whole (3 :<>: 4)
-- Just (Two (Bottom :|-|: Levitate 3) (Levitate 4 :|-|: Top))
--
-- >>> symmetricDifference (1 :<>: 4) (2 :||: 5)
-- Just (Two (1 :<>: 2) (4 :||: 5))
-- @
symmetricDifference ::
  forall x.
  (Ord x) =>
  Interval x ->
  Interval x ->
  Maybe (OneOrTwo (Interval x))
symmetricDifference i1 i2 = case i1 `union` i2 of
  Two j1 j2 -> Just (Two j1 j2)
  One u -> case i1 `intersect` i2 of
    Nothing -> Just (One u)
    Just i -> difference u i

-- | Get the measure of an interval, or 'Nothing' if the interval is infinite.
--
-- @
-- >>> measure (-1 :<>: 1)
-- Just 2
--
-- >>> measure (Bottom :<->: Levitate 1)
-- Nothing
-- @
measure :: forall x. (Ord x, Num x) => Interval x -> Maybe x
measure = measuring subtract

-- | Apply a function to the lower, then upper, endpoint of an interval.
--
-- @
-- >>> measuring const (-1 :<>: 1)
-- Just (-1)
--
-- >>> measuring (*) (4 :<>: 6)
-- Just 24
-- @
-- > measure == measuring subtract
measuring ::
  forall y x.
  (Ord x, Num y) =>
  (x -> x -> y) ->
  Interval x ->
  Maybe y
measuring f = \case
  Levitate l :---: Levitate u -> Just (f l u)
  l :---: u
    | l == u -> Just 0
    | otherwise -> Nothing

-- | Get the distance between two intervals.
--
-- @
-- >>> hausdorff (3 :<>: 5) (6 :<>: 7)
-- Just 1
--
-- >>> hausdorff (3 :<>: 5) Whole
-- Just 0
-- @
hausdorff :: (Ord x, Num x) => Interval x -> Interval x -> Maybe x
hausdorff i1 i2 = case adjacency i1 i2 of
  Before (_ :---: a) (b :---: _) -> levMaybe $ liftA2 (-) b a
  After (_ :---: a) (b :---: _) -> levMaybe $ liftA2 (-) b a
  _ -> Just 0
 where
  levMaybe = foldLevitated Nothing Just Nothing

-- | @m '+/-' r@ creates the closed interval centred at @m@ with radius @r@.
--
-- For the open interval, simply write @'open' (x '+/-' y)@.
(+/-) :: (Ord x, Num x) => x -> x -> Interval x
m +/- r = m - r :||: m + r

-- | Full containment.
isSubsetOf :: (Ord x) => Interval x -> Interval x -> Bool
isSubsetOf i j = case adjacency i j of
  Before{} -> False
  Meets{} -> False
  Overlaps{} -> False
  Starts{} -> True
  During{} -> True
  Finishes{} -> True
  Identical{} -> True
  FinishedBy{} -> False
  Contains{} -> False
  StartedBy{} -> False
  OverlappedBy{} -> False
  MetBy{} -> False
  After{} -> False
