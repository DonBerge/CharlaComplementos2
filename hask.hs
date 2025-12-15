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

----------------------------------------------

data Tree a = E | L a | N (Tree a) a (Tree a) deriving Show

data TreeF a x = E_F | L_F a | N_F x a x
  deriving (Show,Eq, Functor)

out :: Tree a -> TreeF a (Tree a)
out E = E_F
out (L x) = L_F x
out (N l x r) = N_F l x r

outInv :: TreeF a (Tree a) -> Tree a
outInv E_F = E
outInv (L_F x) = L x
outInv (N_F l x r) = N l x r

ana :: (b -> TreeF a b) -> b -> Tree a
ana f = outInv . fmap (ana f) . f

-- Podemos usar ana para generalizar la generación de árboles:

-- Generar un arbol binario completo de altura n con etiquetas n
hasta :: Int -> Tree Int
hasta n = ana gen n
  where
    gen x
      | x==0 = E_F
      | x==1 = L_F x
      | otherwise = N_F (x-1) x (x-1)

-- Generar un arbol binario infinito con etiquetas n
infinito:: a -> Tree a
infinito x = ana gen x
  where
    gen x = N_F x x x
