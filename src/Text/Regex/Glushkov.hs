-- |
-- Module:     Text.Regex.Glushkov
-- Copyright:  (c) Sergey Vinokurov 2023
-- License:    Apache-2.0 (see LICENSE)
-- Maintainer: serg.foo@gmail.com

{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -ddump-simpl -dsuppress-uniques -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-type-applications -dsuppress-coercions -dppr-cols200 -ddump-to-file #-}

module Text.Regex.Glushkov
  ( Fix(..)
  , cata
  , para
  , Regex
  , RegexF
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

-- import Data.Vector.Primitive.Mutable qualified as PM
import Codec.Binary.UTF8.String
import Data.Char
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as GM
import Data.Vector.Primitive qualified as P
import Data.Word

import Prettyprinter.Combinators
import Prettyprinter.Generics (ppGeneric)

import Control.Monad
import Control.Monad.ST
import Control.Monad.State
import Data.Coerce
import Data.Kind (Type)
import Data.Monoid hiding (All)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Array qualified as TA
import Data.Text.Internal qualified as TI
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import GHC.Exts (dataToTag#, tagToEnum#, Int(..))
import GHC.Generics (Generic)
import Prelude hiding (sum)
import Unsafe.Coerce

newtype Fix (f :: Type -> Type) = Fix { unFix :: f (Fix f) }
  deriving stock (Generic)

deriving instance Eq (f (Fix f))   => Eq (Fix f)
deriving instance Ord (f (Fix f))  => Ord (Fix f)

instance Show (f (Fix f)) => Show (Fix f) where
  showsPrec n x = showParen (n > 10) $ showString "Fix " . showsPrec 11 (unFix x)


cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = go
  where
    go = alg . fmap go . unFix

_cataM :: (Traversable f, Monad m) => (f a -> m a) -> Fix f -> m a
_cataM alg = go
  where
    go = alg <=< traverse go . unFix

_cataM_ :: (Traversable f, Monad m) => (f () -> m ()) -> Fix f -> m ()
_cataM_ alg = go
  where
    go = alg <=< traverse go . unFix

_zygo :: Functor f => (f (a, b, c) -> a) -> (f b -> b) -> (f c -> c) -> Fix f -> a
_zygo f g h = (\(a, _, _) -> a) . go
  where
    go
      = (\x -> (f x, g ((\(_, b, _) -> b) <$> x), h ((\(_, _, c) -> c) <$> x)))
      . fmap go
      . unFix

para :: forall f a. Functor f => (f (a, Fix f) -> a) -> Fix f -> a
para alg = go
  where
    go = alg . fmap (\term -> (go term, term)) . unFix

_paraM :: forall f a m. (Traversable f, Monad m) => (f (a, Fix f) -> m a) -> Fix f -> m a
_paraM alg = go
  where
    go = alg <=< traverse (\term -> (, term) <$> go term) . unFix

paraM_ :: forall f m. (Traversable f, Monad m) => (f (Fix f) -> m ()) -> Fix f -> m ()
paraM_ alg = go
  where
    go = alg <=< traverse (\term -> term <$ go term) . unFix


data RegexF a
  = Eps
  | All -- Symbol that matches anything, i.e. ".". NB special kind of symbol bearing it's own mark
  | Sym !Word8
  | Or  a a
  | Seq a a
  | Rep a
  | And a a
  deriving stock (Show, Generic)

instance Functor RegexF  where
  {-# INLINE fmap #-}
  fmap f = \case
    Eps      -> Eps
    All      -> All
    re@Sym{} -> unsafeCoerce re
    Or  a b  -> Or (f a) (f b)
    Seq a b  -> Seq (f a) (f b)
    Rep a    -> Rep (f a)
    And a b  -> And (f a) (f b)

instance Foldable RegexF  where
  {-# INLINE foldMap #-}
  foldMap f = \case
    Eps     -> mempty
    All     -> mempty
    Sym{}   -> mempty
    Or  a b -> f a <> f b
    Seq a b -> f a <> f b
    Rep a   -> f a
    And a b -> f a <> f b

instance Traversable RegexF  where
  {-# INLINE traverse #-}
  traverse f = \case
    Eps      -> pure Eps
    All      -> pure All
    re@Sym{} -> pure $ unsafeCoerce re
    Or  a b  -> Or <$> f a <*> f b
    Seq a b  -> Seq <$> f a <*> f b
    Rep a    -> Rep <$> f a
    And a b  -> And <$> f a <*> f b

type Regex = Fix RegexF

-- Indexed regexp
data IRegexF a
  = IEps !Int
  | IAll !Int -- Symbol that matches anything, i.e. ".". NB special kind of symbol bearing it's own mark
  | ISym !Int !Word8
  | IOr  !Int a a
  | ISeq !Int a a
  | IRep !Int a
  | IAnd !Int a a
  deriving stock (Show, Generic)

getIdx :: IRegexF a -> Int
getIdx = \case
  IEps idx     -> idx
  IAll idx     -> idx
  ISym idx _   -> idx
  IOr  idx _ _ -> idx
  ISeq idx _ _ -> idx
  IRep idx _   -> idx
  IAnd idx _ _ -> idx

instance Functor IRegexF where
  {-# INLINE fmap #-}
  fmap f = \case
    re@IEps{}    -> unsafeCoerce re
    re@IAll{}    -> unsafeCoerce re
    re@ISym{}    -> unsafeCoerce re
    IOr  idx a b -> IOr idx (f a) (f b)
    ISeq idx a b -> ISeq idx (f a) (f b)
    IRep idx a   -> IRep idx (f a)
    IAnd idx a b -> IAnd idx (f a) (f b)

instance Foldable IRegexF where
  {-# INLINE foldMap #-}
  foldMap f = \case
    IEps{}     -> mempty
    IAll{}     -> mempty
    ISym{}     -> mempty
    IOr  _ a b -> f a <> f b
    ISeq _ a b -> f a <> f b
    IRep _ a   -> f a
    IAnd _ a b -> f a <> f b

instance Traversable IRegexF where
  {-# INLINE traverse #-}
  traverse f = \case
    re@IEps{}    -> pure $ unsafeCoerce re
    re@IAll{}    -> pure $ unsafeCoerce re
    re@ISym{}    -> pure $ unsafeCoerce re
    IOr  idx a b -> IOr  idx <$> f a <*> f b
    ISeq idx a b -> ISeq idx <$> f a <*> f b
    IRep idx a   -> IRep idx <$> f a
    IAnd idx a b -> IAnd idx <$> f a <*> f b

type IRegex = Fix IRegexF

instance Pretty IRegex where
  pretty = ppGeneric . unFix

instance Pretty (IRegexF IRegex) where
  pretty = ppGeneric

newtype EfficientBool = EfficientBool { unEfficientBool :: Bool }
  deriving newtype (Pretty)

{-# INLINE fromBool #-}
fromBool :: EfficientBool -> Word8
fromBool (EfficientBool x) = fromIntegral (I# (dataToTag# x))

toBool :: Word8 -> EfficientBool
{-# INLINE toBool #-}
toBool x = case fromIntegral x of
  I# y -> EfficientBool (tagToEnum# y)

newtype instance U.MVector s EfficientBool = MV_Bool (P.MVector s Word8)
newtype instance U.Vector    EfficientBool = V_Bool  (P.Vector    Word8)

instance U.Unbox EfficientBool

instance GM.MVector UM.MVector EfficientBool where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicOverlaps #-}
  {-# INLINE basicUnsafeNew #-}
  {-# INLINE basicInitialize #-}
  {-# INLINE basicUnsafeReplicate #-}
  {-# INLINE basicUnsafeRead #-}
  {-# INLINE basicUnsafeWrite #-}
  {-# INLINE basicClear #-}
  {-# INLINE basicSet #-}
  {-# INLINE basicUnsafeCopy #-}
  {-# INLINE basicUnsafeGrow #-}
  basicLength (MV_Bool v) = GM.basicLength v
  basicUnsafeSlice i n (MV_Bool v) = MV_Bool $ GM.basicUnsafeSlice i n v
  basicOverlaps (MV_Bool v1) (MV_Bool v2) = GM.basicOverlaps v1 v2
  basicUnsafeNew n = MV_Bool `fmap` GM.basicUnsafeNew n
  basicInitialize (MV_Bool v) = GM.basicInitialize v
  basicUnsafeReplicate n x = MV_Bool `fmap` GM.basicUnsafeReplicate n (fromBool x)
  basicUnsafeRead (MV_Bool v) i = toBool `fmap` GM.basicUnsafeRead v i
  basicUnsafeWrite (MV_Bool v) i x = GM.basicUnsafeWrite v i (fromBool x)
  basicClear (MV_Bool v) = GM.basicClear v
  basicSet (MV_Bool v) x = GM.basicSet v (fromBool x)
  basicUnsafeCopy (MV_Bool v1) (MV_Bool v2) = GM.basicUnsafeCopy v1 v2
  basicUnsafeMove (MV_Bool v1) (MV_Bool v2) = GM.basicUnsafeMove v1 v2
  basicUnsafeGrow (MV_Bool v) n = MV_Bool `fmap` GM.basicUnsafeGrow v n

instance G.Vector U.Vector EfficientBool where
  {-# INLINE basicUnsafeFreeze #-}
  {-# INLINE basicUnsafeThaw #-}
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicUnsafeIndexM #-}
  {-# INLINE elemseq #-}
  basicUnsafeFreeze (MV_Bool v) = V_Bool `fmap` G.basicUnsafeFreeze v
  basicUnsafeThaw (V_Bool v) = MV_Bool `fmap` G.basicUnsafeThaw v
  basicLength (V_Bool v) = G.basicLength v
  basicUnsafeSlice i n (V_Bool v) = V_Bool $ G.basicUnsafeSlice i n v
  basicUnsafeIndexM (V_Bool v) i = toBool `fmap` G.basicUnsafeIndexM v i
  basicUnsafeCopy (MV_Bool mv) (V_Bool v) = G.basicUnsafeCopy mv v
  elemseq _ = seq

data Context s = Context
  { ctxActive       :: {-# UNPACK #-} !(U.MVector s EfficientBool)
  , ctxMatchesEmpty :: {-# UNPACK #-} !(U.MVector s EfficientBool)
  , ctxFinal        :: {-# UNPACK #-} !(U.MVector s EfficientBool)
  }

_ppContext :: Context s -> ST s (Doc ann)
_ppContext (Context active' matchesEmpty' final') = do
  active''       <- U.freeze active'
  matchesEmpty'' <- U.freeze matchesEmpty'
  final''        <- U.freeze final'
  pure $ ppDictHeader "Context"
    [ "active"       :-> ppVectorWith pretty active''
    , "matchesEmpty" :-> ppVectorWith pretty matchesEmpty''
    , "final"        :-> ppVectorWith pretty final''
    ]

active :: Context s -> IRegexF a -> ST s Bool
active (Context active' _ _) re =
  (coerce :: ST s EfficientBool -> ST s Bool) $ UM.unsafeRead active' idx
  where
    !idx = getIdx re

setActiveFinal :: Context s -> Int -> Bool -> Bool -> ST s ()
setActiveFinal (Context active' _ final') idx isActive isFinal = do
  UM.unsafeWrite active' idx $ EfficientBool isActive
  UM.unsafeWrite final'  idx $ EfficientBool isFinal

matchesEmpty :: Context s -> IRegexF a -> ST s Bool
matchesEmpty (Context _ matchesEmpty' _) =
  (coerce :: ST s EfficientBool -> ST s Bool) . UM.unsafeRead matchesEmpty' . getIdx

final :: Context s -> IRegexF a -> ST s Bool
final (Context active' _ final') re = do
  isActive <- UM.unsafeRead active' idx
  if unEfficientBool isActive
  then (coerce :: ST s EfficientBool -> ST s Bool) $ UM.unsafeRead final' idx
  else pure False
  where
    !idx = getIdx re

finalOnly :: Context s -> IRegexF a -> ST s Bool
finalOnly (Context _ _ final') re =
  (coerce :: ST s EfficientBool -> ST s Bool) $ UM.unsafeRead final' idx
  where
    !idx = getIdx re

activeFinal :: Context s -> IRegexF a -> ST s (Bool, Bool)
activeFinal (Context active' _ final') re = do
  isActive <- UM.unsafeRead active' idx
  if unEfficientBool isActive
  then do
    isFinal <- UM.unsafeRead final' idx
    pure (True, unEfficientBool isFinal)
  else pure (False, False)
  where
    !idx = getIdx re

indexRegex :: Regex -> (IRegex, Int)
indexRegex
  = (`runState` 0)
  . cata ((coerce :: State Int (IRegexF IRegex) -> State Int IRegex) . alg)
  where
    alg :: RegexF (State Int IRegex) -> State Int (IRegexF IRegex)
    alg = \case
      Eps     -> IEps <$> idx
      All     -> IAll <$> idx
      Sym c   -> ISym <$> idx <*> pure c
      Or  a b -> IOr  <$> idx <*> a <*> b
      Seq a b -> ISeq <$> idx <*> a <*> b
      Rep a   -> IRep <$> idx <*> a
      And a b -> IAnd <$> idx <*> a <*> b

    idx :: State Int Int
    idx = do
      !n <- get
      put $! n + 1
      pure n

initContext :: forall s. IRegex -> Int -> ST s (Context s)
initContext r size = do
  !ctx@Context{ctxActive, ctxMatchesEmpty, ctxFinal} <-
    Context <$> UM.new size <*> UM.new size <*> UM.new size
  let initialize :: Int -> Bool -> ST s ()
      initialize idx matchesEmpty' = do
        UM.unsafeWrite ctxActive idx $ EfficientBool False
        UM.unsafeWrite ctxMatchesEmpty idx $ EfficientBool matchesEmpty'
        UM.unsafeWrite ctxFinal idx $ EfficientBool False

      alg :: IRegexF IRegex -> ST s ()
      alg = \case
        IEps idx     -> initialize idx True
        IAll idx     -> initialize idx False
        ISym idx _   -> initialize idx False
        IOr  idx a b -> do
          a' <- matchesEmpty ctx $ unFix a
          b' <- matchesEmpty ctx $ unFix b
          initialize idx (a' || b')
        ISeq idx a b -> do
          a' <- matchesEmpty ctx $ unFix a
          b' <- matchesEmpty ctx $ unFix b
          initialize idx (a' && b')
        IRep idx _   -> initialize idx True
        IAnd idx a b -> do
          a' <- matchesEmpty ctx $ unFix a
          b' <- matchesEmpty ctx $ unFix b
          initialize idx (a' && b')

  paraM_ alg r
  pure ctx

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
    alg :: RegexF String -> String
    alg = \case
      Eps     -> "reps"
      All     -> "rall"
      Sym c   -> "rsym " ++ show c
      Or  p q -> conc2 "ror" p q
      Seq p q -> conc2 "rseq" p q
      Rep r   -> conc1 "rrep" r
      And p q -> conc2 "rand" p q

    conc1 h p   = h ++ " (" ++ p ++ ")"
    conc2 h p q = h ++ " (" ++ p ++ ") (" ++ q ++ ")"

showReExpr :: Regex -> String
showReExpr = para alg
  where
    wrap :: (RegexF Regex  -> Bool) -> (String, Regex) -> String
    wrap parensPred (str, Fix rx) = if parensPred rx
                                    then str
                                    else "(" ++ str ++ ")"
    alg :: RegexF (String, Regex) -> String
    alg = \case
      Eps{}   -> "ε"
      All{}   -> "."
      Sym c   -> [chr $ fromIntegral c]
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
              Eps   -> True
              All   -> True
              Sym{} -> True
              Or{}  -> False
              Seq{} -> True
              Rep{} -> True
              And{} -> False
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

reps :: Regex
reps = Fix Eps

rall :: Regex
rall = Fix All

rsym :: Char -> Regex
rsym c =
  case map (Fix . Sym) $ encodeChar c of
    []     -> reps
    x : xs -> foldr1 rseq (x :| xs)

ror :: Regex -> Regex -> Regex
ror = (Fix .) . Or

rseq :: Regex -> Regex -> Regex
rseq = (Fix .) . Seq

rrep :: Regex -> Regex
rrep = Fix . Rep

rand :: Regex -> Regex -> Regex
rand = (Fix .) . And

fromString :: [Char] -> Regex
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
      Or  p q -> 1 + p + q
      Seq p q -> 1 + p + q
      Rep r   -> 1 + r
      And p q -> 1 + p + q

reversed :: Regex -> Regex
reversed = cata alg
  where
    alg :: RegexF Regex  -> Regex
    alg (Seq p q) = Fix $ Seq q p
    alg r         = Fix r

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

generateStrings :: Int -> [Char] -> Regex -> [String]
generateStrings limit alphabet
  = map unLengthOrdered
  . takeWhile (\x -> measure x < limit)
  . generate
  where
    generate :: Regex -> [LengthOrdered Char]
    generate = cata alg
      where
        alg :: RegexF [LengthOrdered Char] -> [LengthOrdered Char]
        alg = \case
          Eps     -> [LengthOrdered ""]
          All     -> map (LengthOrdered . (:[])) alphabet
          Sym c   -> [LengthOrdered [chr $ fromIntegral c]]
          Or  p q -> union limit p q
          Seq p q -> xprod limit (<>) p q
          Rep r   -> closure limit (<>) mempty r
          And p q -> intersection limit p q

----- matching

-- shiftInit :: Rx -> Char -> Rx
-- shiftInit rx !c = para (markAlg c) rx True
--
-- shift :: Rx -> Char -> Rx
-- shift rx !c = para (markAlg c) rx False
--
-- {-# INLINE markAlg #-}
-- markAlg :: Char -> RxF (Bool -> Rx, Rx) -> Bool -> Rx
-- markAlg !c = \re m -> case re of
--   RxF { reg = Eps }                    -> reps
--   RxF { reg = All }                    -> rall' m
--   RxF { reg = Sym sym }                -> rsym' (m && sym == c) sym
--   RxF { reg = Or (p, _) (q, _) }       -> ror (p m) (q m)
--   RxF { reg = Seq (p, Fix p') (q, _) } -> rseq (p m) (q (final' p' || m && matchesEmpty p'))
--   RxF { reg = Rep (r, Fix r') }        -> rrep $ r $ m || final' r'
--   RxF { reg = And (p, _) (q, _) }      -> rand (p m) (q m)

shiftInit :: Context s -> IRegex -> Word8 -> ST s ()
shiftInit !ctx rx !c = mark ctx c True rx

shift :: Context s -> IRegex -> Word8 -> ST s ()
shift !ctx rx !c = mark ctx c False rx

mark
  :: forall s.
     Context s
  -> Word8
  -> Bool
  -> IRegex
  -> ST s ()
mark !ctx !c = go
  where
    go :: Bool -> IRegex -> ST s ()
    go m (Fix rx) = case rx of
      IEps _                                       -> pure ()
      IAll idx                                     ->
        setActiveFinal ctx idx m m
      ISym idx sym                                 -> do
        let !m' = m && sym == c
        setActiveFinal ctx idx m' m'
      IOr  idx p@(Fix p') q@(Fix q')               -> do
        go m p
        go m q
        (pActive, pFinal) <- activeFinal ctx p'
        (qActive, qFinal) <- activeFinal ctx q'
        setActiveFinal ctx idx (pActive || qActive) (pFinal || qFinal)
      ISeq idx p@(Fix p') q@(Fix q')               -> do
        pMatchesEmpty <- matchesEmpty ctx p'
        pFinalBefore  <- final ctx p'
        let !m' = pFinalBefore || m && pMatchesEmpty
        go m p
        go m' q
        (pActive, pFinal) <- activeFinal ctx p'
        (qActive, qFinal) <- activeFinal ctx q'
        qMatchesEmpty     <- matchesEmpty ctx q'
        setActiveFinal ctx idx (pActive || qActive) (pFinal && qMatchesEmpty || qFinal)
      IRep idx r@(Fix r')                          -> do
        if m
        then go True r
        else do
          wasFinal <- final ctx r'
          go wasFinal r
        (isActive, isFinal) <- activeFinal ctx r'
        setActiveFinal ctx idx isActive isFinal
      IAnd idx p@(Fix p') q@(Fix q')               -> do
        go m p
        go m q
        (pActive, pFinal) <- activeFinal ctx p'
        (qActive, qFinal) <- activeFinal ctx q'
        setActiveFinal ctx idx (pActive && qActive) (pFinal && qFinal)

-- shift' :: Context s -> IRegex -> Char -> ST s ()
-- shift' ctx rx c = do
--   isActive <- active ctx (unFix rx)
--   when isActive $
--     shift ctx rx c

match :: Regex -> Text -> Bool
match r str = runST $ do
  ctx <- initContext ir size
  if T.null str
  then matchesEmpty ctx $ unFix ir
  else do
    (_, _, _) <- matchIter ctx ir 0 str
    final ctx $ unFix ir
  where
    (ir, size) = indexRegex r

allMatches :: Regex -> Text -> [Match]
allMatches r str = runST $ do
  !ctx <- initContext ir size
  go ctx 0 [] str
  where
    (ir, size) = indexRegex r
    go :: Context s -> Int -> [Match] -> Text -> ST s [Match]
    go !ctx !offset !acc !input = case T.uncons input of
      Nothing          -> pure $ reverse acc
      Just (_, input') -> do
        (m, matched, input'') <- matchIter ctx ir offset input
        if matched
        then go ctx (offset + mLength m) (m : acc) input''
        else go ctx (offset + 1) acc input'

data Match = Match
  { mOffset :: !Int
  , mLength :: !Int
  } deriving stock (Eq, Ord, Show, Generic)

matchIter :: forall s. Context s -> IRegex -> Int -> Text -> ST s (Match, Bool, Text)
matchIter !ctx !r@(Fix rx) !offset (TI.Text arr off len)
  | len == 0
  = do
    haveMatch <- matchesEmpty ctx $ unFix r
    pure (Match offset 0, haveMatch, T.empty)
  | otherwise = do
    let !c = TA.unsafeIndex arr off
    shiftInit ctx r c
    go False 0 c off (off + 1)
  where
    !end = off + len

    go :: Bool -> Int -> Word8 -> Int -> Int -> ST s (Match, Bool, Text)
    go seenFinal !matchLen !_prev !i !j
      | j >= end
      = do
        isFinal <- final ctx rx
        pure $
          if isFinal
          then (Match offset $ matchLen + 1, True, T.empty)
          else (Match offset matchLen, seenFinal, TI.Text arr i $! len - off + i)
      | otherwise
      = do
        isActive <- active ctx rx
        if isActive
        then do
          let !c = TA.unsafeIndex arr j
          isFinal <- finalOnly ctx rx
          shift ctx r c
          go (seenFinal || isFinal) (matchLen + 1) c j (j + 1)
        else
          pure (Match offset matchLen, seenFinal, TI.Text arr i $! len - off + i)
