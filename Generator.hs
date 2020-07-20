module Generator where

newtype Gen a = Gen (Int -> Either String (Int,a))

instance Functor Gen where
  fmap f (Gen g) = Gen $ \i -> do
    (i',a) <- g i
    return (i', f a)

instance Applicative Gen where
  pure x = Gen (\i -> Right (i,x))
  (Gen f) <*> (Gen x) = Gen $ \i -> do
    (i',f') <- f i
    (i'', x') <- x i'
    return (i'', f' x')
  
instance Monad Gen where
  return = pure
  (Gen g) >>= f = Gen $ \i -> do
    (i', x) <- g i
    let (Gen f') = f x
    f' i'

run :: Int -> Gen a -> Either String a
run n (Gen f) = fmap snd $ f n

err :: String -> Gen a
err = Gen . const . Left

get :: Gen Int
get = Gen $ \i -> Right (i+1,i)