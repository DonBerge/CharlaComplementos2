{-# LANGUAGE DeriveFunctor #-}
--data List a = Nil | Cons a (List a)

type List a = [a]

data ListF a x = NilF | ConsF a x
  deriving (Show,Eq, Functor)

inn :: ListF a (List a) -> List a
inn NilF = []
inn (ConsF x xs) = x:xs

innInv :: List a -> ListF a (List a)
innInv [] = NilF
innInv (x:xs) = ConsF x xs

-- Necesitamos saber a que f-algebra ir, usamos la acción f del F-algebra destino para saberlo. 
cata :: (ListF a b -> b) -> List a -> b
cata f = f . fmap (cata f) . innInv

sumF NilF = 0
sumF (ConsF x xs) = x + xs