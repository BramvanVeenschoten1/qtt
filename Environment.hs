module Environment where

import Core
import Data.Map



{-
showEnv :: Env -> String
showEnv = intercalate "\n" . fmap f . toList . parameters where
  f (x,y) = show x ++ " : " ++ show y
-}