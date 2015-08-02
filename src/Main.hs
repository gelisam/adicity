{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, InstanceSigs, MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies, TypeOperators #-}
module Main where

import Prelude hiding (id, (.))

import Control.Arrow
import Control.Category
import Data.Proxy
import Data.Type.Equality


-- 'a_z' represents the type (a, (b, (..., (z, ())))
data Listy a_z where
    Nily  :: Listy ()
    Consy :: Listy b_z -> Listy (a, b_z)

class LIST a_z where
    listy :: Listy a_z

instance LIST () where
    listy = Nily

instance LIST b_z => LIST (a, b_z) where
    listy = Consy listy


type family Concat a_c d_z where
    Concat ()       d_z = d_z
    Concat (a, b_c) d_z = (a, Concat b_c d_z)

listyAppend :: LIST a_c
            => proxy d_z
            -> (a_c, d_z) -> Concat a_c d_z
listyAppend _ = go listy
  where
    go :: Listy a_c
       -> (a_c, d_z)      -> Concat a_c d_z
       -- (()      , d_z) -> d_z
    go Nily       (()      , d_s) = d_s
       -- ((a, b_c), d_z) -> (a, Concat b_c d_z)
    go (Consy ly) ((a, b_c), d_z) = (a, go ly (b_c, d_z))

listyUnappend :: LIST a_c
              => proxy d_z
              -> Concat a_c d_z -> (a_c, d_z)
listyUnappend _ = go listy
  where
    go :: Listy a_c
       -> Concat a_c d_z      -> (a_c, d_z)
       --                d_z  -> ((), d_z)
    go Nily       d_z        = ((), d_z)
       -- (a, Concat b_c d_z) -> ((a, b_c), d_z)
    go (Consy ly) (a, b_z) = ((a, b_c), d_z)
      where
        (b_c, d_z) = go ly b_z

listyPad :: (LIST a_b, LIST a'_b')
         => proxy c_z
         -> (      a_b ->            a'_b'    )
         -> Concat a_b c_z -> Concat a'_b' c_z
listyPad proxy f = listyUnappend proxy
               >>> first f
               >>> listyAppend proxy

concatUnitProof :: LIST a_z
                => proxy a_z
                -> Concat a_z () :~: a_z
concatUnitProof _ = go listy
  where
    go :: Listy a_z
       -> Concat a_z () :~: a_z
       -- () :~: ()
    go Nily       = Refl
       -- (a, Concat b_z ()) :~: (a, b_z)
    go (Consy ly) = case go ly of
        -- (a, t0) :~: (a, t0)
        Refl -> Refl


class MATCH a_z1 a_z2 where
    type CommonPrefix a_z1 a_z2 :: *
    type Suffix1 a_z1 a_z2 :: *
    type Suffix2 a_z1 a_z2 :: *
    split1Proof :: proxy a_z1 -> proxy a_z2
                -> a_z1 :~: Concat (CommonPrefix a_z1 a_z2) (Suffix1 a_z1 a_z2)
    split2Proof :: proxy a_z1 -> proxy a_z2
                -> a_z2 :~: Concat (CommonPrefix a_z1 a_z2) (Suffix2 a_z1 a_z2)
    swap12Proof :: proxy a_z1 -> proxy a_z2
                -> Concat (Suffix1 a_z1 a_z2) (Suffix2 a_z1 a_z2)
               :~: Concat (Suffix2 a_z1 a_z2) (Suffix1 a_z1 a_z2)

instance MATCH () () where
    type CommonPrefix () () = ()
    type Suffix1 () () = ()
    type Suffix2 () () = ()
    
    split1Proof :: proxy () -> proxy ()
                -> () :~: ()
    split1Proof _ _ = Refl
    
    split2Proof :: proxy () -> proxy ()
                -> () :~: ()
    split2Proof _ _ = Refl
    
    swap12Proof :: proxy () -> proxy ()
                -> () :~: ()
    swap12Proof _ _ = Refl

instance LIST b_z2 => MATCH () (a, b_z2) where
    type CommonPrefix () (a, b_z2) = ()
    type Suffix1 () (a, b_z2) = ()
    type Suffix2 () (a, b_z2) = (a, b_z2)
    
    split1Proof :: proxy () -> proxy (a, b_z2)
                -> () :~: ()
    split1Proof _ _ = Refl
    
    split2Proof :: proxy () -> proxy (a, b_z2)
                -> (a, b_z2) :~: (a, b_z2)
    split2Proof _ _ = Refl
    
    swap12Proof :: proxy () -> proxy (a, b_z2)
                -> (a, b_z2) :~: (a, Concat b_z2 ())
    swap12Proof _ _ = case concatUnitProof (Proxy :: Proxy b_z2) of
        -- (a, t0) :~: (a, t0)
        Refl -> Refl

instance LIST b_z1 => MATCH (a, b_z1) () where
    type CommonPrefix (a, b_z1) () = ()
    type Suffix1 (a, b_z1) () = (a, b_z1)
    type Suffix2 (a, b_z1) () = ()
    
    split1Proof :: proxy (a, b_z1) -> proxy ()
                -> (a, b_z1) :~: (a, b_z1)
    split1Proof _ _ = Refl
    
    split2Proof :: proxy (a, b_z1) -> proxy ()
                -> () :~: ()
    split2Proof _ _ = Refl
    
    swap12Proof :: proxy (a, b_z1) -> proxy ()
                -> (a, Concat b_z1 ()) :~: (a, b_z1)
    swap12Proof _ _ = case concatUnitProof (Proxy :: Proxy b_z1) of
        -- (a, t0) :~: (a, t0)
        Refl -> Refl

instance (a ~ a', MATCH b_z1 b_z2) => MATCH (a, b_z1) (a', b_z2) where
    type CommonPrefix (a, b_z1) (a', b_z2) = (a, CommonPrefix b_z1 b_z2)
    type Suffix1 (a, b_z1) (a', b_z2) = Suffix1 b_z1 b_z2
    type Suffix2 (a, b_z1) (a', b_z2) = Suffix2 b_z1 b_z2
    
    split1Proof :: proxy (a, b_z1) -> proxy (a', b_z2)
                -> (a, b_z1) :~: (a, Concat (CommonPrefix b_z1 b_z2)
                                            (Suffix1      b_z1 b_z2))
    split1Proof _ _ = case split1Proof (Proxy :: Proxy b_z1)
                                       (Proxy :: Proxy b_z2) of
        -- (a, t0) :~: (a, t0)
        Refl -> Refl
    
    split2Proof :: proxy (a, b_z1) -> proxy (a', b_z2)
                -> (a, b_z2) :~: (a, Concat (CommonPrefix b_z1 b_z2)
                                            (Suffix2      b_z1 b_z2))
    split2Proof _ _ = case split2Proof (Proxy :: Proxy b_z1)
                                       (Proxy :: Proxy b_z2) of
        -- (a, t0) :~: (a, t0)
        Refl -> Refl
    
    swap12Proof :: proxy (a, b_z1) -> proxy (a', b_z2)
                -> Concat (Suffix1 b_z1 b_z2) (Suffix2 b_z1 b_z2)
               :~: Concat (Suffix2 b_z1 b_z2) (Suffix1 b_z1 b_z2)
    swap12Proof _ _ = swap12Proof (Proxy :: Proxy b_z1)
                                  (Proxy :: Proxy b_z2)


class Category f => Juxtaposable f where
    (>.>)         :: forall a_d c_z1 c_z2 a'_d'.
                   ( LIST a_d, LIST c_z1, LIST c_z2, LIST a'_d'
                   , MATCH c_z1 c_z2
                   , LIST (CommonPrefix c_z1 c_z2)
                   , LIST (Suffix1      c_z1 c_z2)
                   , LIST (Suffix2      c_z1 c_z2)
                   )
                  => f a_d c_z1 -> f c_z2 a'_d'
                  -> f (Concat a_d   (Suffix2 c_z1 c_z2))
                       (Concat a'_d' (Suffix1 c_z1 c_z2))
    (<.<)         :: forall a_d c_z1 c_z2 a'_d'.
                   ( LIST a_d, LIST c_z1, LIST c_z2, LIST a'_d'
                   , MATCH c_z1 c_z2
                   , LIST (CommonPrefix c_z1 c_z2)
                   , LIST (Suffix1      c_z1 c_z2)
                   , LIST (Suffix2      c_z1 c_z2)
                   )
                  => f c_z2 a'_d' -> f a_d c_z1
                  -> f (Concat a_d   (Suffix2 c_z1 c_z2))
                       (Concat a'_d' (Suffix1 c_z1 c_z2))
    g <.< f = f >.> g

instance Juxtaposable (->) where
    (>.>) :: forall a_d c_z1 c_z2 a'_d' commonPrefix suffix1 suffix2.
           ( LIST a_d, LIST c_z1, LIST c_z2, LIST a'_d'
           , MATCH c_z1 c_z2
           , commonPrefix ~ CommonPrefix c_z1 c_z2
           , suffix1      ~ Suffix1      c_z1 c_z2
           , suffix2      ~ Suffix2      c_z1 c_z2
           , LIST commonPrefix
           , LIST suffix1
           , LIST suffix2
           )
          => (a_d -> c_z1) -> (c_z2 -> a'_d')
          -> Concat a_d   suffix2
          -> Concat a'_d' suffix1
           -- Concat a_d   suffix2
    f >.> g = listyPad proxySuffix2 f
           -- Concat c_z1  suffix2
          >>> listyUnappend proxySuffix2
           -- (c_z1, suffix2)
          >>> first matchySplit1
           -- ((commonPrefix, suffix1), suffix2)
          >>> (\((x,y),z) -> (x,(y,z)))
           -- (commonPrefix, (suffix1, suffix2)
          >>> second (listyAppend proxySuffix2)
           -- (commonPrefix, Concat suffix1 suffix2)
          >>> second matchySwap12
           -- (commonPrefix, Concat suffix2 suffix1)
          >>> second (listyUnappend proxySuffix1)
           -- (commonPrefix, (suffix2, suffix1))
          >>> (\(x,(y,z)) -> ((x,y),z))
           -- ((commonPrefix, suffix2), suffix1)
          >>> first matchyUnsplit2
           -- (c_z2, suffix1)
          >>> listyAppend proxySuffix1
           -- Concat c_z2  suffix1
          >>> listyPad proxySuffix1 g
           -- Concat a'_d' suffix1
      where
        proxy1 :: Proxy c_z1
        proxy1 = Proxy
        
        proxy2 :: Proxy c_z2
        proxy2 = Proxy
        
        proxySuffix1 :: Proxy suffix1
        proxySuffix1 = Proxy
        
        proxySuffix2 :: Proxy suffix2
        proxySuffix2 = Proxy
        
        matchySplit1 :: c_z1 -> (commonPrefix, suffix1)
        matchySplit1 = gcastWith (split1Proof proxy1 proxy2)
                    -- Concat commonPrefix suffix1 -> (commonPrefix, suffix1)
                     $ listyUnappend proxySuffix1
        
        matchyUnsplit2 :: (commonPrefix, suffix2) -> c_z2
        matchyUnsplit2 = gcastWith (split2Proof proxy1 proxy2)
                      -- (commonPrefix, suffix2) -> Concat commonPrefix suffix2
                       $ listyAppend proxySuffix2
        
        matchySwap12 :: Concat suffix1 suffix2 -> Concat suffix2 suffix1
        matchySwap12 = castWith (swap12Proof proxy1 proxy2)


runAdicity_0_1 :: (() -> (a, ()))
               -> a
runAdicity_0_1 f = fst (f ())

adicity_0_1 :: a
            -> () -> (a, ())
adicity_0_1 x () = (x, ())

adicity_1_1 :: (a -> b)
            -> (a, ()) -> (b, ())
adicity_1_1 f = first f

adicity_2_1 :: (a -> b -> c)
            -> (a, (b, ())) -> (c, ())
adicity_2_1 f (x, (y, ())) = (f x y, ())


-- | Depending on which (<.<) you interpret as function composition and which one you
-- interpret as function application, you can interpret the adicity composition below
-- as either of the following. They all give the same result.
-- 
-- >>> (+) (2 * 3) 4
-- 10
-- >>> ((+) . (* 2)) 3 4
-- 10
-- >>> n
-- 10
n :: Int
n = runAdicity_0_1 $ adicity_2_1 (+) <.< adicity_2_1 (*)
                 <.< adicity_0_1 2 <.< adicity_0_1 3 <.< adicity_0_1 4

-- |
-- >>> (+1) . (*2) $ 3
-- 7
-- >>> (+1) $ (*2) 3
-- 7
-- >>> m
-- 7
m :: Int
m = runAdicity_0_1 $ adicity_1_1 (+1) <.< adicity_1_1 (*2)
                 <.< adicity_0_1 3

main :: IO ()
main = do print n
          print m
