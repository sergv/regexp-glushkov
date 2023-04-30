-- |
-- Module:     Text.Regex.Glushkov
-- Copyright:  (c) Sergey Vinokurov 2023
-- License:    Apache-2.0 (see LICENSE)
-- Maintainer: serg.foo@gmail.com

{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module Text.Regex.Glushkov
  ( Fix(..)
  , cata
  , para
  , Regex
  , RegexF
  , Rx
  , RxF(..)
  , reps
  , rall
  , rsym
  , ror
  , rseq
  , rrep
  , rand

  , fromString
  , regexSize
  , reversed

  , Match(..)
  , generateStrings
  , match
  , allMatches
  , matchIter
  ) where

import Data.Kind (Type)
import Data.Monoid hiding (All)
import GHC.Generics (Generic)
import Prelude hiding (sum)

newtype Fix (f :: Type -> Type) = Fix { unFix :: f (Fix f) }
  deriving stock (Generic)

deriving instance Eq (f (Fix f))   => Eq (Fix f)
deriving instance Ord (f (Fix f))  => Ord (Fix f)

instance Show (f (Fix f)) => Show (Fix f) where
  showsPrec n x = showParen (n > 10) $ showString "Fix " . showsPrec 11 (unFix x)


type Alg f a = f a -> a

cata :: Functor f => Alg f a -> Fix f -> a
cata alg = go
  where
    go = alg . fmap go . unFix

-- Want "f (Fix f, a) -> a" instead of general
-- Algebra "Alg f (Fix f, a) = f (Fix f, a) -> (Fix f, a)". There's
-- no point in returning Fix f from algebra since it's going to be ignored
para :: forall f a. Functor f => (f (a, Fix f) -> a) -> Fix f -> a
para alg = go
  where
    go = alg . fmap copyArg . unFix
    copyArg term = (para alg term, term)

data RegexF a
  = Eps
  | All -- Symbol that matches anything, i.e. ".". NB special kind of symbol bearing it's own mark
  | Sym !Char
  | Or  a a
  | Seq a a
  | Rep a
  | And a a
  deriving stock (Functor, Show, Generic)

type Regex = Fix RegexF

data RxF a = RxF
  { active       :: Bool
  , matchesEmpty :: Bool
  , final        :: Bool
  , reg          :: RegexF a
  } deriving stock (Functor, Show, Generic)

type Rx = Fix RxF

final' :: RxF Rx -> Bool
final' rx = active rx && final rx

stripRx :: Rx -> Regex
stripRx = cata alg
  where
    alg :: Alg RxF Regex
    alg = Fix . reg

-- TODO use perttyprinting library here

-- ---- printing
--
-- show_full :: Rx -> IO ()
-- show_full rx = putStrLn $ show_rx 0 rx
--     where
--         ws n = take n $ repeat ' '
--
--         show_rx n rx = let n' = n + 5
--                        in "Rx { active = " ++ show (active rx) ++ ", " ++
--                           "matchesEmpty = " ++ show (matchesEmpty rx) ++ ", " ++
--                           "final = " ++ show (final rx) ++ ",\n" ++
--                           ws n' ++ "reg = " ++ show_reg (n' + 6) (reg rx) ++ "}"
--
--         show_reg n Eps       = "Eps"
--         show_reg n All       = "All"
--         show_reg n (Sym c)   = "Sym " ++ show c
--         show_reg n (Or p q)  = let n' = n + 3
--                                in "Or " ++ "(" ++ show_rx (n' + 1) p ++ ")\n" ++
--                                   ws n' ++ "(" ++ show_rx (n' + 1) q ++ ")"
--         show_reg n (Seq p q) = let n' = n + 4
--                                in "Seq " ++ "(" ++ show_rx (n' + 1) p ++ ")\n" ++
--                                   ws n' ++ "(" ++ show_rx (n' + 1) q ++ ")"
--         show_reg n (Rep r)   = "Rep (" ++ show_rx (n + 5) r ++ ")"
--         show_reg n (And p q) = let n' = n + 4
--                                in "And " ++ "(" ++ show_rx (n' + 1) p ++ ")\n" ++
--                                   ws n' ++ "(" ++ show_rx (n' + 1) q ++ ")"

showReData :: Regex -> String
showReData = cata alg
  where
    alg :: Alg RegexF String
    alg = \case
      Eps     -> "reps"
      All     -> "rall"
      Sym c   -> "rsym " ++ show c
      Or p q  -> conc2 "ror" p q
      Seq p q -> conc2 "rseq" p q
      Rep r   -> conc1 "rrep" r
      And p q -> conc2 "rand" p q

    conc1 h p   = h ++ " (" ++ p ++ ")"
    conc2 h p q = h ++ " (" ++ p ++ ") (" ++ q ++ ")"

showReExpr :: Regex -> String
showReExpr = para alg
  where
    wrap :: (RegexF (Fix RegexF) -> Bool) -> (String, Regex) -> String
    wrap parensPred (str, Fix rx) = if parensPred rx
                                    then str
                                    else "(" ++ str ++ ")"
    alg :: RegexF (String, Regex) -> String
    alg = \case
      Eps     -> "ε"
      All     -> "."
      Sym c   -> [c]
      Or p q  ->
        let parensPred = \case
              Eps   -> True
              All   -> True
              Sym{} -> True
              Or{}  -> True
              Seq{} -> True
              Rep{} -> True
              And{} -> True
        in wrap parensPred p ++ "|" ++ wrap parensPred q
      Seq p q ->
        let parensPred = \case
              Eps    -> True
              All    -> True
              Sym {} -> True
              Or{}   -> False
              Seq{}  -> True
              Rep{}  -> True
              And{}  -> False
        in wrap parensPred p ++ wrap parensPred q
      Rep r   ->
        let parensPred = \case
              Eps   -> True
              All   -> True
              Sym{} -> True
              Or{}  -> False
              Seq{} -> False
              Rep{} -> False
              And{} -> False
        in wrap parensPred r ++ "*"
      And p q ->
        let parensPred = \case
              Eps   -> True
              All   -> True
              Sym{} -> True
              Or{}  -> False
              Seq{} -> True
              Rep{} -> True
              And{} -> True
        in wrap parensPred p ++ "&" ++ wrap parensPred q

instance {-# OVERLAPS #-} Show Regex where
  show x = "\"" ++ showReExpr x ++ "\" {{" ++ showReData x ++ "}}"

----- construction

reps :: Rx
reps = Fix $ RxF
  { active       = False
  , matchesEmpty = True
  , final        = False
  , reg          = Eps
  }

rall :: Rx
rall = Fix $ RxF
  { active       = False
  , matchesEmpty = False
  , final        = False
  , reg          = All
  }

rall' :: Bool -> Rx
rall' fin = Fix $ RxF
  { active       = fin
  , matchesEmpty = False
  , final        = fin
  , reg          = All
  }

rsym :: Char -> Rx
rsym c = Fix $ RxF
  { active       = False
  , matchesEmpty = False
  , final        = False
  , reg          = Sym c
  }

rsym' :: Bool -> Char -> Rx
rsym' fin c = Fix $ RxF
  { active       = fin
  , matchesEmpty = False
  , final        = fin
  , reg          = Sym c
  }

ror :: Rx -> Rx -> Rx
ror (Fix p) (Fix q) = Fix $ RxF
  { active       = active p || active q
  , matchesEmpty = matchesEmpty p || matchesEmpty q
  , final        = final' p || final' q
  , reg          = Or (Fix p) (Fix q)
  }

rseq :: Rx -> Rx -> Rx
rseq (Fix p) (Fix q) = Fix $ RxF
  { active       = active p || active q
  , matchesEmpty = matchesEmpty p && matchesEmpty q
  , final        = final' p && matchesEmpty q || final' q
  , reg          = Seq (Fix p) (Fix q)
  }

rrep :: Rx -> Rx
rrep (Fix r) = Fix $ RxF
  { active       = active r
  , matchesEmpty = True
  , final        = final' r
  , reg          = Rep (Fix r)
  }

rand :: Rx -> Rx -> Rx
rand (Fix p) (Fix q) = Fix $ RxF
  { active       = active p && active q
  , matchesEmpty = matchesEmpty p && matchesEmpty q
  , final        = final' p && final' q
  , reg          = And (Fix p) (Fix q)
  }

fromString :: String -> Rx
fromString []     = reps
fromString [c]    = rsym c
fromString (c:cs) = rseq (rsym c) (fromString cs)

regexSize :: Regex -> Int
regexSize = cata alg
  where
    alg :: RegexF Int -> Int
    alg = \case
      Eps     -> 1
      All     -> 1
      Sym{}   -> 1
      Or p q  -> 1 + p + q
      Seq p q -> 1 + p + q
      Rep r   -> 1 + r
      And p q -> 1 + p + q

reversed :: Rx -> Rx
reversed = cata alg
  where
    alg :: RxF Rx -> Rx
    alg (RxF { reg = Seq p q }) = rseq q p
    alg r                       = Fix r

--- enumeration of language strings

newtype LengthOrdered a = LengthOrdered { unLengthOrdered :: [a] }
  deriving (Show, Eq)

instance (Ord a) => Ord (LengthOrdered a) where
  (LengthOrdered xs) <= (LengthOrdered ys) =
    lenxs < lenys || (lenxs == lenys && xs <= ys)
    where
      lenxs = length xs
      lenys = length ys

instance Semigroup (LengthOrdered a) where
  LengthOrdered xs <> LengthOrdered ys = LengthOrdered $ xs <> ys

instance Monoid (LengthOrdered a) where
  mempty = LengthOrdered []

class Measurable a where
  measure :: a -> Int

instance Measurable [a] where
  measure x = length x

instance Measurable (LengthOrdered a) where
  measure (LengthOrdered x) = measure x

union :: (Ord a, Measurable a) => Int -> [a] -> [a] -> [a]
union _     xs        []        = xs
union _     []        ys        = ys
union limit (x:_)     (y:_)
  | measure x >= limit && measure y >= limit = []
union limit xs@(x:xt) ys@(y:yt) =
  case compare x y of
    LT -> x : union limit xt ys
    EQ -> x : union limit xt yt
    GT -> y : union limit xs yt

intersection :: (Ord a, Measurable a) => Int -> [a] -> [a] -> [a]
intersection _     _         []        = []
intersection _     []        _         = []
intersection limit (x:_)     (y:_)
  | measure x >= limit || measure y >= limit = []
intersection limit (x:xt) ys@(y:yt) =
  if x == y
  then
    x : intersection limit xt yt
  else
    intersection limit xt ys

_difference :: (Ord a, Measurable a) => Int -> [a] -> [a] -> [a]
_difference _     xs        []        = xs
_difference _     []        _         = []
_difference limit (x:_)     _         | measure x >= limit = []
_difference limit xs@(x:xt) ys@(y:yt) =
  case compare x y of
    LT -> x : _difference limit xt ys
    EQ -> _difference limit xt yt
    GT -> _difference limit xs yt

xprod :: (Measurable a, Measurable b, Ord c, Measurable c) =>
      Int -> (a -> b -> c) -> [a] -> [b] -> [c]
xprod _     _ []        _         = []
xprod _     _ _         []        = []
xprod limit _ (x:_)     (y:_)
  | measure x >= limit || measure y >= limit = []
xprod limit f (x:xt) ys@(y:yt) =
  f x y : union limit (xprod limit f [x] yt) (xprod limit f xt ys)

_sequence :: (Ord a) => Int -> [LengthOrdered a] -> [LengthOrdered a] -> [LengthOrdered a]
_sequence limit xs ys = xprod limit (<>) xs ys

closure :: (Ord a, Measurable a) => Int -> (a -> a -> a) -> a -> [a] -> [a]
closure _     _ zr []        = [zr]
closure limit _ _  (x:_)     | measure x >= limit = []
closure limit f zr xs@(x:xt) =
  if zr == x
  then closure limit f zr xt
  else zr : xprod limit f xs (closure limit f zr xs)

generateStrings :: Int -> [Char] -> Rx -> [String]
generateStrings limit alphabet rx
  = map unLengthOrdered
  $ takeWhile (\x -> measure x < limit)
  $ generate
  $ stripRx rx
  where
    generate :: Regex -> [LengthOrdered Char]
    generate = cata alg
      where
        alg :: RegexF [LengthOrdered Char] -> [LengthOrdered Char]
        alg = \case
          Eps     -> [LengthOrdered ""]
          All     -> map (LengthOrdered . (:[])) alphabet
          Sym c   -> [LengthOrdered [c]]
          Or p q  -> union limit p q
          Seq p q -> xprod limit (<>) p q
          Rep r   -> closure limit (<>) mempty r
          And p q -> intersection limit p q

----- matching

shiftInit :: Rx -> Char -> Rx
shiftInit rx c = para (markAlg c) rx True

shift :: Rx -> Char -> Rx
shift rx c = para (markAlg c) rx False

markAlg :: Char -> RxF (Bool -> Rx, Rx) -> Bool -> Rx
markAlg !c re m = case re of
  RxF { reg = Eps }                    -> reps
  RxF { reg = All }                    -> rall' m
  RxF { reg = Sym sym }                -> rsym' (m && sym == c) sym
  RxF { reg = Or (p, _) (q, _) }       -> ror (p m) (q m)
  RxF { reg = Seq (p, Fix p') (q, _) } -> rseq (p m) (q (final' p' || m && matchesEmpty p'))
  RxF { reg = Rep (r, Fix r') }        -> rrep $ r $ m || final' r'
  RxF { reg = And (p, _) (q, _) }      -> rand (p m) (q m)

shift' :: Rx -> Char -> Rx
shift' rx c
  | active (unFix rx)
  = shift rx c
  | otherwise
  = rx

match :: Rx -> String -> Bool
match r [] = matchesEmpty $ unFix r
match r xs = final' r'
  where
    (Fix r', _, _, _) = matchIter r xs

allMatches :: Rx -> [Char] -> [Match]
allMatches r = go
  where
    go [] = []
    go cs@(_ : cs')
      -- | Debug.Trace.trace ("cs = " ++ show cs ++ ", cs' = " ++ show cs' ++ ", cs'' = " ++ show cs'' ++ ", matched = " ++ show matched) $ False = undefined
      | matched   = m : go cs''
      | otherwise = go cs'
      where
        (_, m, matched, cs'') = matchIter r cs

newtype Match = Match [Char]
  deriving stock (Eq, Ord, Show)

matchIter :: Rx -> [Char] -> (Rx, Match, Bool, [Char])
matchIter r []       = (r, Match [], matchesEmpty $ unFix r, [])
matchIter r (c : cs) = go False [] (shiftInit r c) c cs
  where
    go :: Bool -> [Char] -> Rx -> Char -> [Char] -> (Rx, Match, Bool, [Char])
    go seenFinal ms !rx'@(Fix rx) !prev []
      | final' rx
      = (rx', Match $ reverse $ prev : ms, True, [])
      | otherwise
      = (rx', Match $ reverse ms, seenFinal, [prev])
    go seenFinal ms rx'@(Fix rx)  prev xs'@(x:xs)
      | active rx
      = go (seenFinal || final rx) (prev : ms) (shift' rx' x) x xs
      | otherwise
      = (rx', Match $ reverse ms, seenFinal, prev : xs')

-- buildTrickyRegex :: Rx -> Int -> Rx
-- buildTrickyRegex toWrap n = iter n reps reps
--   where
--     iter 0 opt solid = rseq opt (rseq solid opt)
--     iter k opt solid = iter (k - 1) (rseq (ror toWrap reps) opt) (rseq toWrap solid)
