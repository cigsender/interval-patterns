{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Main where

import Algebra.Lattice (Lattice (..))
import Algebra.Lattice.Levitated (Levitated (..))
import Control.Applicative
import Control.Monad
import Data.Interval (
  Interval,
  pattern (:<->:),
  pattern (:<-|:),
  pattern (:<>:),
  pattern (:<|:),
  pattern (:|->:),
  pattern (:|-|:),
  pattern (:|>:),
  pattern (:||:),
 )
import Data.Interval qualified as Interval
import Data.Interval.Borel (Borel)
import Data.Interval.Borel qualified as Borel
import Data.Interval.Layers qualified as Layers
import Data.List qualified as List
import Data.Semigroup
import GHC.TypeNats
import Test.Hspec
import Test.QuickCheck
import Text.Parsec (sepBy, try)
import Text.Parsec.Char (char, digit, spaces, string)
import Text.Parsec.Text (Parser)
import Text.ParserCombinators.Parsec (choice)

type family Ints (n :: Nat) x where
  Ints 0 x = x
  Ints n x = Int -> Ints (n - 1) x

main :: IO ()
main = hspec do
  describe "smart constructors" do
    it "orient finite intervals" do
      property @(Ints 2 _) \x y -> when (x > y) do
        (x :<>: y) `shouldBe` (y :<>: x)
        (x :|>: y) `shouldBe` (y :<|: x)
        (x :<|: y) `shouldBe` (y :|>: x)
        (x :||: y) `shouldBe` (y :||: x)
        (Levitate x :<->: Levitate y) `shouldBe` (Levitate y :<->: Levitate x)
        (Levitate x :|->: Levitate y) `shouldBe` (Levitate y :<-|: Levitate x)
        (Levitate x :<-|: Levitate y) `shouldBe` (Levitate y :|->: Levitate x)
        (Levitate x :|-|: Levitate y) `shouldBe` (Levitate y :|-|: Levitate x)

    it "orient infinite intervals" do
      (Top :<->: Bottom) `shouldBe` (Bottom :<->: Top :: Interval Int)
      (Top :|->: Bottom) `shouldBe` (Bottom :<-|: Top :: Interval Int)
      (Top :<-|: Bottom) `shouldBe` (Bottom :|->: Top :: Interval Int)
      (Top :|-|: Bottom) `shouldBe` (Bottom :|-|: Top :: Interval Int)

    it "close point intervals" do
      property @(Int -> _) \x -> do
        (x :<>: x) `shouldBe` (x :||: x)
        (x :|>: x) `shouldBe` (x :||: x)
        (x :<|: x) `shouldBe` (x :||: x)
        (x :||: x) `shouldBe` (x :||: x)
        (Levitate x :<->: Levitate x) `shouldBe` (Levitate x :|-|: Levitate x)
        (Levitate x :|->: Levitate x) `shouldBe` (Levitate x :|-|: Levitate x)
        (Levitate x :<-|: Levitate x) `shouldBe` (Levitate x :|-|: Levitate x)
        (Levitate x :|-|: Levitate x) `shouldBe` (Levitate x :|-|: Levitate x)

    it "intersect" do
      property @(Ints 4 _) \a b c d -> do
        let [x, y, z, w] = List.sort [a, b, c, d]
        when (x /= y && y /= z && z /= w) do
          (x :<>: z `Interval.intersect` y :<>: w) `shouldBe` Just (z :<>: y)
          (x :<|: z `Interval.intersect` y :|>: w) `shouldBe` Just (z :||: y)
          (x :|>: z `Interval.intersect` y :<|: w) `shouldBe` Just (z :<>: y)
          (x :||: z `Interval.intersect` y :||: w) `shouldBe` Just (z :||: y)
    it "union" do
      property @(Ints 4 _) \a b c d -> do
        let [x, y, z, w] = List.sort [a, b, c, d]
        when (x /= y && y /= z && z /= w) do
          (x :<>: z `Interval.union` y :<>: w) `shouldBe` Interval.One (x :<>: w)
          (x :<|: z `Interval.union` y :|>: w) `shouldBe` Interval.One (x :<>: w)
          (x :|>: z `Interval.union` y :<|: w) `shouldBe` Interval.One (x :||: w)
          (x :||: z `Interval.union` y :||: w) `shouldBe` Interval.One (x :||: w)
          when (y < z) do
            (x :<>: y `Interval.union` z :<>: w) `shouldBe` Interval.Two (x :<>: y) (z :<>: w)
            (x :<|: y `Interval.union` z :|>: w) `shouldBe` Interval.Two (x :<|: y) (z :|>: w)
            (x :|>: y `Interval.union` z :<|: w) `shouldBe` Interval.Two (x :|>: y) (z :<|: w)
            (x :||: y `Interval.union` z :||: w) `shouldBe` Interval.Two (x :||: y) (z :||: w)
    it "unions" do
      property @(Ints 8 _) \a b c d e f g h -> do
        let [z, y, x, w, v, u, t, s] = List.sort [a, b, c, d, e, f, g, h]
        Interval.unions [z :||: v, y :||: u, x :||: t, w :||: s] `shouldBe` [z :||: s]

  describe "Borel intervals" do
    it "(<>) is commutative" do
      property @(Ints 4 _) \a b x y -> do
        let abxy = Borel.singleton (a :<>: b) <> Borel.singleton (x :<>: y)
            xyab = Borel.singleton (x :<>: y) <> Borel.singleton (a :<>: b)
        abxy `shouldBe` xyab
    it "(<>) is associative" do
      property @(Ints 6 _) \a b m n x y -> do
        let ab = Borel.singleton (a :<>: b)
            mn = Borel.singleton (m :<>: n)
            xy = Borel.singleton (x :<>: y)
        (ab <> mn) <> xy `shouldBe` ab <> (mn <> xy)

  describe "Layers" do
    it "(<>) is associative" do
      property @(Ints 9 _) \a b c d e f x y z -> do
        let abx = Layers.singleton (a :<>: b) (Sum x)
            cdy = Layers.singleton (c :||: d) (Sum y)
            efz = Layers.singleton (e :<>: f) (Sum z)
        (abx <> cdy) <> efz `shouldBe` abx <> (cdy <> efz)

newtype Version = Version [Int]
  deriving (Eq, Ord, Show)

version :: Parser Version
version = Version <$> sepBy (read <$> many digit) (char '.')

data Tk
  = TkAnd
  | TkOr
  | TkBorel (Borel Version)
  | TkOpen
  | TkClose

tk :: Parser Tk
tk =
  choice
    [ try tkAnd
    , try tkOr
    , try do liftM2 ((TkBorel . Borel.singleton) .) tkCmp tkVersion
    , try tkOpen
    , try tkClose
    ]
 where
  tkAnd = TkAnd <$ (spaces *> string "&&" <* spaces)
  tkOr = TkOr <$ (spaces *> string "||" <* spaces)
  tkVersion = spaces *> version <* spaces
  tkCmp =
    choice
      [ (Bottom :<-|:) . Levitate <$ try do string "<="
      , (Bottom :<->:) . Levitate <$ try do string "<"
      , (:|->: Top) . Levitate <$ try do string ">="
      , (:<->: Top) . Levitate <$ try do string ">"
      , Interval.point <$ try do string "=="
      ]
  tkOpen = TkOpen <$ (spaces *> string "(" <* spaces)
  tkClose = TkClose <$ (spaces *> string ")" <* spaces)

foldTk :: [Tk] -> Borel Version
foldTk = \case
  [TkBorel b] -> b
  TkOpen : TkBorel b0 : TkAnd : TkBorel b1 : TkClose : rest ->
    foldTk do TkBorel (b0 /\ b1) : rest
  TkOpen : TkBorel b0 : TkOr : TkBorel b1 : TkClose : rest ->
    foldTk do TkBorel (b0 \/ b1) : rest
  TkBorel b0 : TkAnd : TkOpen : rest ->
    foldTk do TkBorel b0 : TkAnd : [TkBorel (foldTk (TkOpen : rest))]
  TkBorel b0 : TkOr : TkOpen : rest ->
    foldTk do TkBorel b0 : TkOr : [TkBorel (foldTk (TkOpen : rest))]
  TkBorel b0 : TkAnd : TkBorel b1 : rest -> foldTk do TkBorel (b0 /\ b1) : rest
  TkBorel b0 : TkOr : TkBorel b1 : rest -> foldTk do TkBorel (b0 \/ b1) : rest
  TkOpen : TkBorel b : TkClose : rest -> foldTk do TkBorel b : rest
  _ -> error "malformed bounds"

versionBounds :: Parser (Borel Version)
versionBounds = foldTk <$> many tk

-- >>> Text.Parsec.parse versionBounds "" ">= 2.0.0 && <3"
-- Right (Borel (fromList [(Version [2,0,0] :|>: Version [3])]))

-- >>> Text.Parsec.parse versionBounds "" ">= 4"
-- Right (Borel (fromList [(Levitate (Version [4]) :|->: Top)]))

-- >>> Text.Parsec.parse versionBounds "" "(>= 1.2 && <3) || (>= 4.0 && < 5)"
-- Right (Borel (fromList [(Version [1,2] :|>: Version [3]),(Version [4,0] :|>: Version [5])]))

-- >>> Text.Parsec.parse versionBounds "" "(>= 1.2 && <3) || (>= 2.0 && < 5)"
-- Right (Borel (fromList [(Version [1,2] :|>: Version [5])]))
