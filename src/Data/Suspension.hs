module Data.Suspension
  ( Suspension (..),
    suspension,
    meridToMaybe,
    fromMerid,
    withMerid,
    whenMerid,
    meridToEither,
  )
where

import Data.Data (Data)
import Data.Group (Group (..))

-- | The 'Suspension' of a type is its two-point extension:
-- a "south pole" 'Nadir' and a "north pole" 'Zenit', if each value
-- of the underlying type is considered as a 'Merid'ian.
data Suspension x
  = Nadir
  | Merid !x
  | Zenit
  deriving
    ( Eq,
      Ord,
      Show,
      Read,
      Generic,
      Data,
      Typeable,
      Functor,
      Foldable,
      Traversable
    )

instance Bounded (Suspension x) where
  minBound = Nadir
  maxBound = Zenit

instance (Ord x, Enum x, Bounded x) => Enum (Suspension x) where
  toEnum = \case
    0 -> Nadir
    n | pred n > fromEnum (maxBound @x) -> Zenit
    n -> Merid (toEnum (pred n))
  fromEnum = \case
    Nadir -> 0
    Merid n -> 1 + fromEnum n
    Zenit -> succ (fromEnum @x maxBound)

instance Applicative Suspension where
  pure = Merid

  Nadir <*> _ = Nadir
  Merid f <*> x = fmap f x
  Zenit <*> _ = Zenit

instance Monad Suspension where
  Nadir >>= _ = Nadir
  Merid x >>= f = f x
  Zenit >>= _ = Zenit

instance (Semigroup x) => Semigroup (Suspension x) where
  Nadir <> x = x
  Zenit <> _ = Zenit
  x <> Nadir = x
  _ <> Zenit = Zenit
  Merid x <> Merid y = Merid (x <> y)

instance (Monoid x) => Monoid (Suspension x) where
  mempty = Merid mempty

instance (Group x) => Group (Suspension x) where
  invert = \case
    Nadir -> Zenit
    Merid x -> Merid (invert x)
    Zenit -> Nadir

instance (Num x) => Num (Suspension x) where
  Nadir + Zenit = error "tried to perform Nadir + Zenit"
  Nadir + _ = Nadir
  _ + Nadir = Nadir
  Zenit + _ = Zenit
  _ + Zenit = Zenit
  Merid x + Merid y = Merid (x + y)

  Nadir * Zenit = error "tried to perform Nadir * Zenit"
  Nadir * _ = Nadir
  _ * Nadir = Nadir
  Zenit * _ = Zenit
  _ * Zenit = Zenit
  Merid x * Merid y = Merid (x * y)

  abs = \case
    Merid x -> Merid (abs x)
    _ -> Zenit

  signum = \case
    Nadir -> Merid (-1)
    Merid x -> Merid (signum x)
    Zenit -> Merid 1

  negate = \case
    Nadir -> Zenit
    Merid x -> Merid (negate x)
    Zenit -> Nadir

  fromInteger = Merid . fromInteger

-- |
-- @
--   suspension nadir merid zenit = \\case
--     Nadir -> nadir
--     Merid a -> merid a
--     Zenit -> zenit
-- @
suspension :: y -> (x -> y) -> y -> Suspension x -> y
suspension nadir merid zenit = \case
  Nadir -> nadir
  Merid x -> merid x
  Zenit -> zenit
{-# INLINE suspension #-}

-- | Unsafely extract the value from a 'Merid'.
fromMerid :: HasCallStack => Suspension x -> x
fromMerid = \case
  Nadir -> error "expected Merid but got Nadir!"
  Merid a -> a
  Zenit -> error "expected Merid but got Zenit!"

-- | Safely extract the value from a 'Merid'.
meridToMaybe :: Suspension x -> Maybe x
meridToMaybe = withMerid id
{-# INLINE meridToMaybe #-}

-- | Safely extract the value from a 'Merid',
-- providing in case of failure whether the argument was 'Zenit'.
meridToEither :: Suspension x -> Either Bool x
meridToEither = suspension (Left False) Right (Left True)
{-# INLINE meridToEither #-}

-- | Apply the function to the inner value, if it exists.
withMerid :: (Alternative m) => (x -> y) -> Suspension x -> m y
withMerid f = suspension empty (pure . f) empty
{-# INLINE withMerid #-}

-- | Execute the action using the inner value, if it exists.
whenMerid :: (Alternative m) => Suspension x -> (x -> m ()) -> m ()
whenMerid s f = suspension pass f pass s
{-# INLINE whenMerid #-}
