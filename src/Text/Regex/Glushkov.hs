-- |
-- Module:     Text.Regex.Glushkov
-- Copyright:  (c) Sergey Vinokurov 2023
-- License:    Apache-2.0 (see LICENSE)
-- Maintainer: serg.foo@gmail.com

{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE PatternSynonyms      #-}
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
import Data.Bits hiding (shift, And)
import Data.Char
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as GM
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
import GHC.Exts (dataToTag#, Int(..), isTrue#, eqWord8#)
import GHC.Word (Word8(..))
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

cataM :: (Traversable f, Monad m) => (f a -> m a) -> Fix f -> m a
cataM alg = go
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

_paraM_ :: forall f m. (Traversable f, Monad m) => (f (Fix f) -> m ()) -> Fix f -> m ()
_paraM_ alg = go
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


newtype EfficientBool = EfficientBool { unEfficientBool :: Int }
  deriving newtype (Pretty)

pattern ETrue :: EfficientBool
pattern ETrue  = EfficientBool 1

pattern EFalse :: EfficientBool
pattern EFalse = EfficientBool 0

fromBool :: Bool -> EfficientBool
fromBool x = (EfficientBool (I# (dataToTag# x)))

fromEqWord8 :: Word8 -> Word8 -> EfficientBool
fromEqWord8 (W8# a) (W8# b) = EfficientBool (I# (eqWord8# a b))

toBool :: EfficientBool -> Bool
toBool (EfficientBool (I# x)) = isTrue# x

toInt :: EfficientBool -> Int
toInt (EfficientBool x) = x

-- toInt# :: EfficientBool -> Int#
-- toInt# (EfficientBool (I# x)) = x

-- {-# INLINE bnot #-}
-- bnot :: EfficientBool -> EfficientBool
-- bnot (EfficientBool x) = EfficientBool (1 - x)

{-# INLINE band #-}
band :: EfficientBool -> EfficientBool -> EfficientBool
band (EfficientBool x) (EfficientBool y) = EfficientBool (x .&. y)

{-# INLINE bor #-}
bor :: EfficientBool -> EfficientBool -> EfficientBool
bor (EfficientBool x) (EfficientBool y) = EfficientBool (x .|. y)

newtype ActiveFinalMatchesEmptyEntry = ActiveFinalMatchesEmptyEntry
  { unActiveFinalMatchesEmptyEntry :: Word8 }
  deriving stock (Eq, Ord, Show)

newtype instance U.MVector s ActiveFinalMatchesEmptyEntry = MV_Int (U.MVector s Word8)
newtype instance U.Vector    ActiveFinalMatchesEmptyEntry = V_Int  (U.Vector    Word8)
deriving instance GM.MVector U.MVector ActiveFinalMatchesEmptyEntry
deriving instance G.Vector   U.Vector  ActiveFinalMatchesEmptyEntry
instance U.Unbox ActiveFinalMatchesEmptyEntry

getActive :: ActiveFinalMatchesEmptyEntry -> EfficientBool
getActive = (fromEqWord8 0x01 . (.&. 0x01)) . unActiveFinalMatchesEmptyEntry

getFinal :: ActiveFinalMatchesEmptyEntry -> EfficientBool
getFinal = (fromEqWord8 0x02 . (.&. 0x02)) . unActiveFinalMatchesEmptyEntry

getMatchesEmpty :: ActiveFinalMatchesEmptyEntry -> EfficientBool
getMatchesEmpty = (fromEqWord8 0x04 . (.&. 0x04)) . unActiveFinalMatchesEmptyEntry

mkActiveFinalMatchesEmpty :: EfficientBool -> EfficientBool -> EfficientBool -> ActiveFinalMatchesEmptyEntry
mkActiveFinalMatchesEmpty active final matchesEmpty = ActiveFinalMatchesEmptyEntry $
  boolToWord8 active       * 0x01 .|.
  boolToWord8 final        * 0x02 .|.
  boolToWord8 matchesEmpty * 0x04

{-# INLINE boolToWord8 #-}
boolToWord8 :: EfficientBool -> Word8
boolToWord8 = fromIntegral . unEfficientBool

-- assignActiveFinal :: Bool -> Bool -> ActiveFinalMatchesEmptyEntry -> ActiveFinalMatchesEmptyEntry
-- assignActiveFinal active final (ActiveFinalMatchesEmptyEntry x) =
--   ActiveFinalMatchesEmptyEntry $
--     boolToWord8 active * 0x01 .|.
--     boolToWord8 final  * 0x02 .|.
--     x .&. 0x4

newtype Context s = Context
  { _ctxItems :: U.MVector s ActiveFinalMatchesEmptyEntry
  }

_ppContext :: Context s -> ST s (Doc ann)
_ppContext (Context items) = do
  items' <- U.freeze items
  pure $ ppDictHeader "Context"
    [ "active"       :-> ppVectorWith (pretty . getActive) items'
    , "matchesEmpty" :-> ppVectorWith (pretty . getFinal) items'
    , "final"        :-> ppVectorWith (pretty . getMatchesEmpty) items'
    ]

getEntry :: Context s -> Int -> ST s ActiveFinalMatchesEmptyEntry
getEntry (Context items) = UM.unsafeRead items

setEntry :: Context s -> Int -> ActiveFinalMatchesEmptyEntry -> ST s ()
setEntry (Context items) = UM.unsafeWrite items

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
  !ctx <- Context <$> UM.new size
  let initialize :: Int -> EfficientBool -> ST s EfficientBool
      initialize idx matchesEmpty' = do
        setEntry ctx idx $ mkActiveFinalMatchesEmpty EFalse EFalse matchesEmpty'
        pure matchesEmpty'

      alg :: IRegexF EfficientBool -> ST s EfficientBool
      alg = \case
        IEps idx     -> initialize idx ETrue
        IAll idx     -> initialize idx EFalse
        ISym idx _   -> initialize idx EFalse
        IOr  idx a b -> do
          initialize idx (a `bor` b)
        ISeq idx a b -> do
          initialize idx (a `band` b)
        IRep idx _   -> initialize idx ETrue
        IAnd idx a b -> do
          initialize idx (a `band` b)

  _ <- cataM alg r
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

shiftInit :: Context s -> IRegex -> Word8 -> ST s ()
shiftInit !ctx rx !c = mark ctx c ETrue rx

shift :: Context s -> IRegex -> Word8 -> ST s ()
shift !ctx rx !c = mark ctx c EFalse rx

mark
  :: forall s.
     Context s
  -> Word8
  -> EfficientBool
  -> IRegex
  -> ST s ()
mark !ctx !c = go
  where
    go :: EfficientBool -> IRegex -> ST s ()
    go !m (Fix rx) = case rx of
      IEps _                                       -> pure ()
      IAll idx                                     ->
        setEntry ctx idx $ mkActiveFinalMatchesEmpty m m EFalse
      ISym idx sym                                 -> do
        let !m' = m `band` fromEqWord8 sym c
        setEntry ctx idx $ mkActiveFinalMatchesEmpty m' m' EFalse
      IOr  idx p@(Fix p') q@(Fix q')               -> do
        go m p
        go m q
        !p'' <- getEntry ctx $ getIdx p'
        !q'' <- getEntry ctx $ getIdx q'
        setEntry ctx idx $ ActiveFinalMatchesEmptyEntry $
          unActiveFinalMatchesEmptyEntry p'' .|. unActiveFinalMatchesEmptyEntry q''

      ISeq idx p@(Fix p') q@(Fix q')               -> do
        let !pIdx = getIdx p'
            !qIdx = getIdx q'
        !pEntryBefore <- getEntry ctx pIdx
        let !pMatchesEmpty = getMatchesEmpty pEntryBefore
            !pFinalBefore  = getFinal pEntryBefore
        let !m' = pFinalBefore `bor` (m `band` pMatchesEmpty)
        go m p
        go m' q
        !pEntryAfter <- getEntry ctx pIdx
        !qEntryAfter <- getEntry ctx qIdx
        let !qMatchesEmpty = getMatchesEmpty qEntryAfter
        setEntry ctx idx $ mkActiveFinalMatchesEmpty
          (getActive pEntryAfter `bor` getActive qEntryAfter)
          ((getFinal pEntryAfter `band` qMatchesEmpty) `bor` getFinal qEntryAfter)
          (pMatchesEmpty `band` qMatchesEmpty)
      IRep idx r@(Fix r')                          -> do
        let !rIdx = getIdx r'
        if toBool m
        then go ETrue r
        else do
          !wasFinal <- getFinal <$> getEntry ctx rIdx
          go wasFinal r
        !rEntryAtfer <- getEntry ctx rIdx
        setEntry ctx idx $ mkActiveFinalMatchesEmpty
          (getActive rEntryAtfer)
          (getFinal rEntryAtfer)
          ETrue
      IAnd idx p@(Fix p') q@(Fix q')               -> do
        go m p
        go m q
        !p'' <- getEntry ctx $ getIdx p'
        !q'' <- getEntry ctx $ getIdx q'
        setEntry ctx idx $ ActiveFinalMatchesEmptyEntry $
          unActiveFinalMatchesEmptyEntry p'' .&. unActiveFinalMatchesEmptyEntry q''

-- shift' :: Context s -> IRegex -> Char -> ST s ()
-- shift' ctx rx c = do
--   isActive <- active ctx (unFix rx)
--   when isActive $
--     shift ctx rx c

match :: Regex -> Text -> Bool
match r str = runST $ do
  ctx <- initContext ir size
  if T.null str
  then toBool . getMatchesEmpty <$> getEntry ctx (getIdx (unFix ir))
  else do
    (_, _, _) <- matchIter ctx ir 0 str
    toBool . getFinal <$> getEntry ctx (getIdx (unFix ir))
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
    haveMatch <- getMatchesEmpty <$> getEntry ctx (getIdx (unFix r))
    pure (Match offset 0, toBool haveMatch, T.empty)
  | otherwise = do
    let !c = TA.unsafeIndex arr off
    shiftInit ctx r c
    go EFalse 0 c off (off + 1)
  where
    !end = off + len

    go :: EfficientBool -> Int -> Word8 -> Int -> Int -> ST s (Match, Bool, Text)
    go !seenFinal !matchLen !_prev !i !j
      | j >= end
      = do
        isFinal <- getFinal <$> getEntry ctx (getIdx rx)
        pure $
          if toBool isFinal
          then (Match offset $ matchLen + 1, True, T.empty)
          else (Match offset matchLen, toBool seenFinal, TI.Text arr i $! len - off + i)
      | otherwise
      = do
        entry <- getEntry ctx (getIdx rx)
        if toBool $ getActive entry
        then do
          let !c = TA.unsafeIndex arr j
          shift ctx r c
          go (seenFinal `bor` getFinal entry) (matchLen + 1) c j (j + 1)
        else
          pure (Match offset matchLen, toBool seenFinal, TI.Text arr i $! len - off + i)
