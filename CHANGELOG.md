# Revision history for interval-patterns

##

* `unBorel :: (Ord x) => Borel x -> [Interval x]`, the ordered list of intervals in the `Borel` set

## 0.8.0

* `newtype Shrink x = Shrink {getShrink :: Borel x}`, the monoid formed by `Borel.intersection` and `whole`
* `landAbove :: (Ord x, Ord y) => y -> Layers x y -> Borel x` above "sea level"
* `land :: (Ord x, Monoid y, Ord y) => Layers x y -> Borel x` above a "sea level" of `mempty`
* remove unnecessary `Lattice` constraints on the endpoints of `Borel` sets
* fix `Constr` definitions having an extra `-` character
* fix bug in `difference` conflating the cases `Finishes` and `FinishedBy`

## 0.7.2

* fix sign of result in `Data.Timeframe.duration`
* generalize `within` and `thickness` to Levitated

## 0.7.1

* instances `Hashable` and `NFData` for `Interval`
* relax constraint on `Data.Interval.Layers.thickness` to `Semigroup`

## 0.7.0.3

* update `lattice` version range to build on new stackage LTS

## 0.7.0.2

* fix bug in `Data.Interval.hull`
* improve documentation of `Data.Interval`

## 0.7.0.1

* use `heaps` to improve performance of `Layers` at the cost of an `Ord` constraint on the "height" of the layers

## 0.6.0.1

* drop `relude` dependency

## 0.5.1.0 - 2022-08-04

* improve performance of `Layers.fromList`

## 0.5.0.0 - 2022-08-04

* fix direction of `diffUTCTime` in `erlangs`
* Remove export of `Data.Interval.Layers.nestingsAsc`
  * also fix its implementation
  * rely on `nestings` for external use

## 0.4.0.0 - 2022-07-26

* New functions
  * unidirectional `pattern (:--:)` for matching finite intervals regardless of `Bound`
  * `Data.Interval.Layers.integrate` for calculating areas
  * `Data.Calendar.erlangs` for calculating carried load
  * `pile`, flipped synonym for `Data.Interval.Layers.insert`
  * rename `Data.Interval.Borel.cutout` to `remove`, flipped infix synonym `(\-)`
  * rename `Data.Interval.Borel.clip` to `truncate`, flipped infix synonym `(\=)`
  * rename previous `Data.Interval.Layers.remove` to `dig`
  * new function `Data.Interval.Layers.remove` akin to `Borel`, flipped infix synonym `(\-)`
  * rename `Data.Interval.Layers.clip` to `truncate`, flipped infix synonym `(\=)`
* New instances
  * `Data`, `Typeable`, `Generic` instances for `Interval`
  * `Data` instance for `Adjacency`
* Minor improvements
  * better implementation of `unions`
  * fix comparison order in `compareBounds`
  * removed `compareBounds`' forced restriction to `Levitated`
  * `imin`, `iinf`, `isup`, `imax` no longer return `Bound`s
  * fix `difference` in cases `MetBy` and `After`
  * fix regression in smart constructor ordering
  * fix `within` on boundaries
  * add example to `measuring`
  * improve implementation of `unionsAsc`
  * better `Show` instance for finite intervals

## 0.3.1.0 - 2022-07-13

* re-export `OneOrTwo` from `Data.Interval`

## 0.3.0.1 - 2022-06-08

* expose `Data.Calendar` lol

## 0.3.0.0 - 2022-06-08

* new pattern synonym `(:---:) :: (Ord x) => Levitated x -> Levitated x -> Interval x`
  * only works as a pattern; cannot be used as an expression
  * disregards the open/closedness of the boundary
* fix `openclosed` and `closedopen`
* rename `imapS -> imapLev` and `itraverseS -> itraverseLev` following `Suspension -> Levitated`
* `(...)` as a value-level analogue to `interval`
* `Data.Interval.isSubsetOf`
* `Data.Interval.Borel.isSubsetOf`
* `Data.Interval.Layers.difference`
* `Data.Interval.Layers.clip`
* `Data.Interval.Layers.toStepFunction`
* `Data.Calendar.happeningAt`

## 0.2.0.1 - 2022-05-30

* export `clip` from `Data.Interval.Borel`

## 0.2.0.0 - 2022-05-30

* generalize `Layers` to arbitrary `Num` types and `Calendar` to arbitrary `Real` types

## 0.1.0.0 - 2022-05-19

* constructors behave more intuitively
  * if the endpoints are equal, it becomes a closed interval
  * when endpoints are reversed, using a smart constructor preserves the declared endpoint boundaries
    (e.g. `6 :|>: 4` becomes `4 :<|: 6`)
* tests

## 0.0.11.0 - 2022-03-08

* drop `Data.Suspension` entirely in favour of `Algebra.Lattice.Levitated`
* rename `Data.Interval.{Set => Borel}` and add Lattice/Ring/Heyting instances
* explicit exports for `Data.OneOrTwo`

## 0.0.10.2 -- 2022-02-22

* fix `Enum` for `Suspension`

## 0.0.10.1 -- 2022-02-15

* add `Layers.remove` and `Layers.baseline`

## 0.0.10.0 -- 2022-02-15

* add dependency `group-theory`
* `instance Monoid Suspension` now lifts monoids only
* add `instance Group x => Group (Suspension x)`
* `Data.Interval.unions` now sorts the list first; add `unionsAsc`
* `Covering.unionsSet` uses `from/toAscList` and `unionsAsc`
* `instance Group y => Group (Layers x y)`
* `instance Functor Layers`
* `nesting` now sorts the list first; add `nestingAsc`
* `Semigroup Layers` uses `nestingAsc`

## 0.0.9.0 -- 2022-02-15

* `Layers` is now a two-parameter type, and `nestings` supports arbitrary
  semigroups instead of the previous restriction to `Int`.
* drop `multiset` dependency as a result
* `type Event = Layers UTCTime (Sum Int)`

## 0.0.8.0 -- 2022-02-15

* switch definitions of `lower` and `lowerBound`, `upper` and `upperBound`
* universal `Bounded` and lifted `Enum` for Suspension
* `(Data.Interval.\\)`
* change names from `IntervalSet -> Covering` and `IntervalLayer -> Layers`
* rename `Covering.intervals` to `Covering.covering` ("smart constructor")

## 0.0.7.1 -- 2022-02-13

* `imapS` and `itraverseS`

## 0.0.7.0 -- 2022-02-13

* introduce strictness annotations for `Suspension`, `Interval`, and `Adjacency`

## 0.0.6.1 -- 2022-02-13

* fix `Num` instance for `Suspension`

## 0.0.6.0 -- 2022-02-13

* remove `AdjacencyRepr` (don't need a type parameter you're just gonna hide)
* amalgamate `split` into `adjacency`
* no need for weird import chain, define everything in `Data.Interval`

## 0.0.5.0 -- 2022-02-12

* `Data.Interval.Layered` provides a monoid like `IntervalSet`, but
  that will keep track of the number of times a particular interval
  has been added to the structure. This is useful for determining, e.g.,
  how many clones you need to attend all today's meetings on time.

## 0.0.4.0 -- 2022-02-12

* Rename project

# Revision history for timeframes

## 0.0.3.0 -- 2022-02-12

* Drop `orient`, putting `Ord` constraints on the constructors of `Interval`
  and leaving the ordering to the smart constructors
* Rewrite `intersection`, `union`, and `difference` using `split`
* Settle on changelog format
* move `withBounds` to `Data.Interval`

## 0.0.2.0 -- 2022-02-12

* Drop `UpToThree` in favour of a more dependently-typed model of adjacency
* `Overlap` is changed to `Adjacency` where it occurs
* `split` now returns `SomeAdjacency`, which can be pattern-matched to yield
  the exact (one, two, or three) intervals into which the two have been cleaved
* `Interval` moved into `Data.Interval.Types` to avoid a cyclic dependency
  between `Data.Interval` and `Data.Interval.Adjacency`

## 0.0.1.0 -- 2022-02-08

Types and functions for working with intervals and their monoid under union.

* `Data.Suspension` provides the two-point extension of a type,
  used for marking the endpoints of intervals.
* `Data.Interval` defines the `Interval` type, along with type- and value-level
  structures for working with closed and open endpoints.
* `overlap` calculates the relationship between intervals
  according to Allen`s interval algebra.
* `split` separates two intervals into one, two, or three parts,
  depending on their overlap.
