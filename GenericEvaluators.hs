{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}



data Intro intro s b a
  = Intro intro [a] [s -> b]


data Reducible elim spec m s b a
  = Elim elim m [a] [s -> b]
  | Special spec [a] [s -> b]


data Term intro elim spec
  = Var String
  | I (Intro intro
             (Term intro elim spec)
             (Term intro elim spec)
             (Term intro elim spec))
  | R (Reducible elim spec
         (Term intro elim spec)
         (Term intro elim spec)
         (Term intro elim spec)
         (Term intro elim spec))


class Aux f where
  mapAux :: (a -> a') -> f s b a -> f s b a'


instance Aux (Intro intro) where
  mapAux f (Intro i as scs) = Intro i (map f as) scs


instance Aux (Reducible elim spec m) where
  mapAux f (Elim e m as scs)  = Elim e m (map f as) scs
  mapAux f (Special s as scs) = Special s (map f as) scs


mapMain :: (m -> m')
        -> Reducible elim spec m s b a -> Reducible elim spec m' s b a
mapMain f (Elim e m as scs)  = Elim e (f m) as scs
mapMain _ (Special s as scs) = Special s as scs


type Redex intro elim spec a
  = Reducible elim spec (Intro intro a a a) a a a


type IntroTerm intro elim spec
  = Intro intro
      (Term intro elim spec)
      (Term intro elim spec)
      (Term intro elim spec)


class Reduce intro elim spec where
  reduce :: Redex intro elim spec a -> a


-- Lazy Evaluation

lazyEval :: Reduce intro elim spec
         => Term intro elim spec
         -> IntroTerm intro elim spec
lazyEval (I i) = i
lazyEval (R r) = lazyEval (reduce (mapMain lazyEval r))


-- Eager Evaluation

eagerEval :: Reduce intro elim spec
          => Term intro elim spec
          -> IntroTerm intro elim spec
eagerEval (I i) = mapAux (I . eagerEval) i
eagerEval (R r) = eagerEval (reduce (mapAux (I . eagerEval)
                                            (mapMain eagerEval r)))


-- Stacks

data Stack frame intro elim spec
  = [frame intro elim spec] :>: Term intro elim spec
  | [frame intro elim spec] :<: IntroTerm intro elim spec


-- Lazy Stack Machines

data LazyFrame intro elim spec
  = LazyFrame elim
              [Term intro elim spec]
              [Term intro elim spec -> Term intro elim spec]

stackLazy :: forall intro elim spec.
             Reduce intro elim spec
          => Term intro elim spec
          -> IntroTerm intro elim spec
stackLazy tm = let [] :<: i = go ([] :>: tm)
               in i
  where
    go :: Stack LazyFrame intro elim spec -> Stack LazyFrame intro elim spec
    go (fms :>: I i)
      = fms :<: i
    go (fms :>: R (Elim e m as scs))
      = go ((LazyFrame e as scs:fms) :>: m)
    go (fms :>: R (Special s as scs))
      = go (fms :>: reduce r)
      where
        r :: Redex intro elim spec (Term intro elim spec)
        r = Special s as scs
    go ((LazyFrame e as scs:fms) :<: ret)
      = go (fms :>: reduce r)
      where
        r :: Redex intro elim spec (Term intro elim spec)
        r = Elim e ret as scs
    go s = s


-- Eager Stack Machines

data EagerFrame intro elim spec
  = EagerFrameElimMain elim
                       [Term intro elim spec]
                       [Term intro elim spec -> Term intro elim spec]
  | EagerFrameElimAux elim
                      (IntroTerm intro elim spec)
                      [IntroTerm intro elim spec]
                      [Term intro elim spec]
                      [Term intro elim spec -> Term intro elim spec]
  | EagerFrameIntro intro
                    [IntroTerm intro elim spec]
                    [Term intro elim spec]
                    [Term intro elim spec -> Term intro elim spec]
  | EagerFrameSpecial spec
                      [IntroTerm intro elim spec]
                      [Term intro elim spec]
                      [Term intro elim spec -> Term intro elim spec]

stackEager :: forall intro elim spec.
              Reduce intro elim spec
           => Term intro elim spec
           -> IntroTerm intro elim spec
stackEager tm = let [] :<: i = go ([] :>: tm)
                in i
  where
    go :: Stack EagerFrame intro elim spec -> Stack EagerFrame intro elim spec
    go (fms :>: I (Intro i [] scs))
      = go (fms :<: Intro i [] scs)
    go (fms :>: I (Intro i (a:as) scs))
      = go ((EagerFrameIntro i [] as scs:fms) :>: a)
    go (fms :>: R (Elim e m as scs))
      = go ((EagerFrameElimMain e as scs:fms) :>: m)
    go (fms :>: R (Special s [] scs))
      = go (fms :>: reduce r)
      where
        r :: Redex intro elim spec (Term intro elim spec)
        r = Special s [] scs
    go ((EagerFrameIntro i as' [] scs:fms) :<: a')
      = go (fms :<: Intro i (map I (reverse (a':as'))) scs)
    go ((EagerFrameIntro i as' (a:as) scs:fms) :<: a')
      = go ((EagerFrameIntro i (a':as') as scs:fms) :>: a)
    go ((EagerFrameElimMain e [] scs:fms) :<: m')
      = go (fms :>: reduce r)
      where
        r :: Redex intro elim spec (Term intro elim spec)
        r = Elim e m' [] scs
    go ((EagerFrameElimMain e (a:as) scs:fms) :<: m')
      = go ((EagerFrameElimAux e m' [] as scs:fms) :>: a)
    go ((EagerFrameElimAux e m' as' [] scs:fms) :<: a')
      = go (fms :>: reduce r)
      where
        r :: Redex intro elim spec (Term intro elim spec)
        r = Elim e m' (map I (reverse (a':as'))) scs
    go ((EagerFrameElimAux e m' as' (a:as) scs:fms) :<: a')
      = go ((EagerFrameElimAux e m' (a':as') as scs:fms) :>: a)
    go ((EagerFrameSpecial s as' [] scs:fms) :<: a')
      = go (fms :>: reduce r)
      where
        r :: Redex intro elim spec (Term intro elim spec)
        r = Special s (map I (reverse (a':as'))) scs
    go ((EagerFrameSpecial s as' (a:as) scs:fms) :<: a')
      = go ((EagerFrameSpecial s (a':as') as scs:fms) :>: a)
    go s = s



-- The Simply Typed Lambda Calculus

data STLCIntro = Pair | Lam | InL | InR
data STLCElim = Fst | Snd | App | Case
data STLCSpecial = Let

pattern Pair' x y = Intro Pair [x,y] []
pattern Fst' p = Elim Fst p [] []
pattern Snd' p = Elim Snd p [] []

pattern Lam' f = Intro Lam [] [f]
pattern App' f x = Elim App f [x] []

pattern InL' x = Intro InL [x] []
pattern InR' y = Intro InR [y] []
pattern Case' d f g = Elim Case d [] [f,g]

pattern Let' x f = Special Let [x] [f]

instance Reduce STLCIntro STLCElim STLCSpecial where
  reduce (Fst' (Pair' x _))   = x
  reduce (Snd' (Pair' _ y))   = y
  reduce (App' (Lam' f) x)    = f x
  reduce (Case' (InL' x) f _) = f x
  reduce (Case' (InR' y) _ g) = g y
  reduce (Let' x f)           = f x
