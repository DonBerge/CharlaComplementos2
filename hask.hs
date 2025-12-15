{-# LANGUAGE DeriveFunctor #-}

-- Minimax: Dos jugadores comienzan en la raiz de un arbol finito. En cada
-- turno pueden elegir si ir a la rama izquierda o la derecha del arbol.
-- El puntaje final es la suma de los valores de los nodos visitados.
-- Un jugador siempre trata de maximizar el puntaje mientras otro trata
-- de minimizarlo. ¿Cual es el puntaje final?

data TreeF a x = E_F | N_F x a x deriving Functor

a1 :: (Num p, Ord p) => TreeF p (a, p) -> p
a1 E_F = 0
a1 (N_F l v r) = v + (snd l `max` snd r)

a2 :: (Num p, Ord p) => TreeF p (p, b) -> p
a2 E_F = 0
a2 (N_F l v r) = v + (fst l `min` fst r)

data Tree a = E | N (Tree a) a (Tree a) deriving Show

split :: (a->b) -> (a->c) -> (a->(b,c))
split f g x = (f x,g x)

outInv :: Tree a -> TreeF a (Tree a)
outInv E = E_F
outInv (N l x r) = N_F l x r

maximize :: Tree Int -> Int
maximize = a1 . fmap (split maximize minimize) . outInv

minimize :: Tree Int -> Int
minimize = a2 . fmap (split maximize minimize) . outInv

someTree :: Tree Int
someTree = N (N E 2 E) 3 (N E 4 E)
