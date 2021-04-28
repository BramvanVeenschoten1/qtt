module Modulesystem where

import Data.Map
import Data.List
import Data.Either
import Control.Monad

import Prettyprint
import Declaration
import Elaborator
import Lexer(Loc)
import Parser
import qualified Core as C
import Core
import Debug.Trace

checkModules :: [Module] -> Either String String
checkModules mods = case checkProgram (mods, Data.Map.empty, emptyObjects, 0) of
  Left err -> Left (show err)
  Right (_,global_names,obs,_) -> pure (showGlobalNames obs global_names)

checkProgram :: ([Module],GlobalNames,Objects,Int) -> Either Error ([Module],GlobalNames, Objects,Int)
checkProgram (glob @ ([], _,_,_)) = pure glob
checkProgram (mod:mods, names, obs, fresh) =
  checkModule mod [] (mods, names, obs, fresh) >>= checkProgram

checkModule :: Module -> [String] -> ([Module],GlobalNames,Objects,Int) -> Either Error ([Module],GlobalNames, Objects,Int)
checkModule (mod_name,imports,decls) in_progress globnobs = do
  --trace (show mod_name ++ " " ++ show in_progress ++ "\n") (pure ())

  let circularities = Data.List.intersect imports (mod_name : in_progress)
      
      checkCircularities
        | Prelude.null circularities = pure ()
        | otherwise = Left ("circular imports: " ++ intercalate " " circularities)
      
      checkDependency (globs @ (unverified, global_names, _, _)) dep_name
        | Data.Map.member dep_name global_names = pure globs
        | otherwise = case find (\(name,_,_) -> name == dep_name) unverified of
          Nothing -> Left ("unknown module name: " ++ dep_name)
          Just dep -> checkModule dep (mod_name : in_progress) globs
  
  checkCircularities
  
  (unverified,global_names,objects,freshNames) <- foldM checkDependency globnobs imports
  
  let imported_names = Data.Map.foldrWithKey (\key names acc -> if elem key imports then mergeNameSpace names acc else acc) emptyNameSpace global_names
      
      unverified' = Data.List.filter (\(name,_,_) -> not (Data.Map.member name global_names)) unverified
      
      st = ElabState {
        newName = freshNames,
        moduleName = mod_name,
        importedNames = imported_names,
        internalNames = emptyNameSpace,
        globalObjects = objects}
  
  st' <- foldM checkDecl st decls
  
  pure (unverified', Data.Map.insert mod_name (internalNames st') global_names, globalObjects st', newName st')