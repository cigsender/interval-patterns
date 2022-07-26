module Data.Interval.Borel (
  Borel,
  borel,
  intervalSet,
  Data.Interval.Borel.empty,
  singleton,
  Data.Interval.Borel.null,
  insert,
  whole,
  remove,
  (\-),
  truncate,
  (\=),
  member,
  notMember,
  union,
  unions,
  difference,
  symmetricDifference,
  complement,
  intersection,
  intersections,
  hull,
  isSubsetOf,
) where

import Algebra.Heyting (Heyting ((==>)))
import Algebra.Lattice
import Data.Data
import Data.Interval (Interval)
import Data.Interval qualified as I
import Data.OneOrTwo (OneOrTwo (..))
import Data.Semiring (Ring, Semiring)
import Data.Semiring qualified as Semiring
import Data.Set qualified as Set
import Prelude hiding (null, truncate)

-- | The 'Borel' sets on a type are the sets generated by its intervals.
-- It forms a 'Heyting' algebra with 'union' as join and 'intersection' as meet,
-- and a 'Ring' with 'symmetricDifference' as addition and 'intersection' as
-- multiplication (and 'complement' as negation). In fact the algebra is Boolean
-- as the operation @x '==>' y = 'complement' x '\/' y@.
--
-- It is a monoid that is convenient for agglomerating
-- groups of intervals, such as for calculating the overall timespan
-- of a group of events. However, it is agnostic of
-- how many times each given point has been covered.
-- To keep track of this data, use 'Data.Interval.Layers'.
newtype Borel x = Borel (Set (Interval x))
  deriving (Eq, Ord, Show, Generic, Typeable, Data)

instance (Ord x) => One (Borel x) where
  type OneItem _ = Interval x
  one = singleton

instance (Ord x) => Semigroup (Borel x) where
  Borel is <> Borel js = Borel (unionsSet (is <> js))

instance (Ord x) => Monoid (Borel x) where
  mempty = Borel mempty

instance (Ord x, Lattice x) => Lattice (Borel x) where
  (\/) = union
  (/\) = intersection

instance (Ord x, Lattice x) => BoundedMeetSemiLattice (Borel x) where
  top = whole

instance (Ord x, Lattice x) => BoundedJoinSemiLattice (Borel x) where
  bottom = mempty

instance (Ord x, Lattice x) => Heyting (Borel x) where
  x ==> y = complement x \/ y

instance (Ord x, Lattice x) => Semiring (Borel x) where
  plus = symmetricDifference
  times = intersection
  zero = mempty
  one = whole

instance (Ord x, Lattice x) => Ring (Borel x) where
  negate = complement

-- | Consider the 'Borel' set identified by a list of 'Interval's.
borel :: (Ord x) => [Interval x] -> Borel x
borel = Borel . Set.fromList . I.unions

-- | Turn a 'Borel' set into a 'Set.Set' of 'Interval's.
intervalSet :: (Ord x) => Borel x -> Set (Interval x)
intervalSet (Borel is) = unionsSet is

unionsSet :: (Ord x) => Set (Interval x) -> Set (Interval x)
unionsSet = Set.fromAscList . I.unionsAsc . Set.toAscList

-- | The empty 'Borel' set.
empty :: (Ord x) => Borel x
empty = Borel Set.empty

-- | The 'Borel' set consisting of a single 'Interval'.
singleton :: (Ord x) => Interval x -> Borel x
singleton x = Borel (Set.singleton x)

-- | Is this 'Borel' set empty?
null :: Borel x -> Bool
null (Borel is) = Set.null is

-- | Insert an 'Interval' into a 'Borel' set, agglomerating along the way.
insert :: (Ord x) => Interval x -> Borel x -> Borel x
insert i (Borel is) = Borel (unionsSet (Set.insert i is))

-- | The maximal 'Borel' set, that covers the entire range.
whole :: (Ord x) => Borel x
whole = Borel (Prelude.one I.Whole)

-- |
-- Completely remove an 'Interval' from a 'Borel' set.
-- Essentially the opposite of 'truncate'.
remove :: (Ord x) => Interval x -> Borel x -> Borel x
remove i (Borel is) =
  flip foldMap is $
    (I.\\ i) >>> \case
      Nothing -> mempty
      Just (One j) -> borel [j]
      Just (Two j k) -> borel [j, k]

-- | Flipped infix version of 'remove'.
(\-) :: (Ord x) => Borel x -> Interval x -> Borel x
(\-) = flip remove

-- | Is this point 'I.within' any connected component of the 'Borel' set?
member :: (Ord x) => x -> Borel x -> Bool
member x (Borel is) = any (I.within x) is

-- | Is this point not 'I.within' any connected component of the 'Borel' set?
notMember :: (Ord x) => x -> Borel x -> Bool
notMember x = not . member x

-- | A synonym for '(<>)'.
union :: (Ord x) => Borel x -> Borel x -> Borel x
union = (<>)

-- | A synonym for 'fold'.
unions :: (Ord x) => [Borel x] -> Borel x
unions = fold

-- | Remove all intervals of the second set from the first.
difference :: (Ord x) => Borel x -> Borel x -> Borel x
difference is (Borel js) = foldr remove is js

-- | Take the symmetric difference of two 'Borel' sets.
symmetricDifference :: (Ord x) => Borel x -> Borel x -> Borel x
symmetricDifference is js = difference is js <> difference js is

-- | Take the 'Borel' set consisting of each point not in the given one.
complement :: (Ord x) => Borel x -> Borel x
complement = difference whole

-- | Given an 'Interval' @i@, @'truncate' i@ will trim a 'Borel' set
-- so that its 'hull' is contained in @i@.
truncate :: (Ord x) => Interval x -> Borel x -> Borel x
truncate i (Borel js) =
  foldr ((<>) . maybe mempty one . I.intersect i) mempty js

-- | Flipped infix version of 'truncate'.
(\=) :: (Ord x) => Borel x -> Interval x -> Borel x
(\=) = flip truncate

-- | Take the intersection of two 'Borel' sets.
intersection :: (Ord x) => Borel x -> Borel x -> Borel x
intersection is (Borel js) = foldMap (`truncate` is) js

-- | Take the intersection of a list of 'Borel' sets.
intersections :: (Ord x) => [Borel x] -> Borel x
intersections [] = mempty
intersections [i] = i
intersections (i : j : js) = intersection (intersection i j) (intersections js)

-- | Take the smallest spanning 'Interval' of a 'Borel' set,
-- provided that it is not the empty set.
hull :: (Ord x) => Borel x -> Maybe (Interval x)
hull (Borel js) = Set.minView js <&> \(i, is) -> I.hulls (i :| Set.toAscList is)

isSubsetOf :: (Ord x) => Borel x -> Borel x -> Bool
isSubsetOf is js = null $ difference is js
