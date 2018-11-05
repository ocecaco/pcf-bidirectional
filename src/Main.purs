module Main where

import Prelude
import Effect (Effect)
import Effect.Console (logShow)
import Data.Either (Either)
import Data.List (List(Nil), (:), (!!))
import Data.Generic.Rep.Show (genericShow)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Control.Monad.Reader.Trans (ReaderT, ask, local, runReaderT)
import Control.Monad.Except.Trans (ExceptT, throwError, runExceptT)
import Data.Identity (Identity(..))
import Partial.Unsafe (unsafeCrashWith)

-- unimplemented :: forall a. a
-- unimplemented = unsafeCrashWith "unimplemented"

data Ty = TyInt
        | TyArrow Ty Ty

derive instance eqTy :: Eq Ty
derive instance genericTy :: Generic Ty _

instance showTy :: Show Ty where
  show t = genericShow t

renderType :: Ty -> String
renderType TyInt = "int"
renderType (TyArrow ty1 ty2) = "(" <> renderType ty1 <> " -> " <> renderType ty2 <> ")"

data BinOp = Plus | Times

derive instance genericBinOp :: Generic BinOp _

instance showBinOp :: Show BinOp where
  show t = genericShow t

newtype Scope = Scope Term

derive instance genericScope :: Generic Scope _

instance showScope :: Show Scope where
  show t = genericShow t

data Term = BVar Int
          | FVar String
          | App Term Term
          | Abs Scope
          | Fix Scope

          | Zero
          | Succ Term
          | EqZero Term Term Scope

          | Ascribe Term Ty

derive instance genericTerm :: Generic Term _

instance showTerm :: Show Term where
  show t = genericShow t

type TyCheck a = ReaderT Context (ExceptT String Identity) a

newtype Context = Context (List Ty)

emptyContext :: Context
emptyContext = Context Nil

extendContext :: Context -> Ty -> Context
extendContext (Context ctxt) ty = Context (ty:ctxt)

getContext :: TyCheck Context
getContext = ask

lookupVar :: Int -> TyCheck Ty
lookupVar idx = do
  Context ctxt <- getContext
  case ctxt !! idx of
    Nothing -> bail "index out of range"
    Just ty -> pure ty

checkTyEqual :: Ty -> Ty -> TyCheck Unit
checkTyEqual ty1 ty2
  | ty1 == ty2 = pure unit
  | otherwise = bail ("type mismatch: expected " <> show ty1 <> " but found " <> show ty2)

bail :: forall a. String -> TyCheck a
bail msg = throwError msg

checkType :: Term -> Ty -> TyCheck Unit
checkType (Abs (Scope tm)) ty = do
  case ty of
    TyArrow ty1 ty2 -> local (\ctxt -> extendContext ctxt ty1) (checkType tm ty2)
    _ -> bail "expected function type for abstraction"

checkType (Fix (Scope tm)) ty = local (\ctxt -> extendContext ctxt ty) (checkType tm ty)

checkType (EqZero t z (Scope s)) ty = do
  checkType t TyInt
  checkType z ty
  local (\ctxt -> extendContext ctxt TyInt) (checkType s ty)

checkType tm ty = do
  ty' <- inferType tm
  checkTyEqual ty ty'

inferType :: Term -> TyCheck Ty
inferType (BVar idx) = lookupVar idx
inferType (FVar _) = bail "found free variable"
inferType (App t1 t2) = do
  funty <- inferType t1
  case funty of
    TyArrow argty retty -> do
      checkType t2 argty
      pure retty
    _ -> bail "expected function type for application"

inferType (Ascribe tm ty) = do
  checkType tm ty
  pure ty

inferType Zero = pure TyInt
inferType (Succ t) = do
  checkType t TyInt
  pure TyInt

inferType (Abs _) = bail "cannot infer type"
inferType (Fix _) = bail "cannot infer type"
inferType (EqZero _ _ _) = bail "cannot infer type"

infer :: Term -> Either String Ty
infer tm = ty
  where Identity ty = runExceptT (runReaderT (inferType tm) emptyContext)

substitute :: Term -> Scope -> Term
substitute sub (Scope sc) = go 0 sc
  where go n v@(BVar k)
          | n == k = sub
          | otherwise = v

        go n v@(FVar x) = v

        go n (App t1 t2) = App (go n t1) (go n t2)
        go n (Abs (Scope body)) = Abs (Scope (go (n+1) body))
        go n (Fix (Scope body)) = Fix (Scope (go (n+1) body))

        go n v@Zero = v
        go n (Succ t) = Succ (go n t)

        go n (EqZero t z (Scope s)) = EqZero (go n t) (go n z) (Scope (go (n+1) s))

        go n (Ascribe t1 ty) = Ascribe (go n t1) ty

eval :: Term -> Term
eval (App t1 t2) =
  case eval t1 of
    Abs body -> eval (substitute (eval t2) body)
    _ -> unsafeCrashWith "attempt to apply non-function"

eval f@(Fix tm) = eval (substitute f tm)

eval (Ascribe t _) = eval t

eval (BVar _) = unsafeCrashWith "found bound var"
eval (FVar _) = unsafeCrashWith "found free var"

eval t@(Abs _) = t
eval t@Zero = t
eval (Succ t) = Succ (eval t)

eval (EqZero t z s) =
  case eval t of
    Zero -> eval z
    Succ x -> eval (substitute x s)
    _ -> unsafeCrashWith "expected number"

adder :: Term
adder = Ascribe (Fix (Scope (Abs (Scope (Abs (Scope (EqZero (BVar 1) (BVar 0) (Scope (Succ (App (App (BVar 3) (BVar 0)) (BVar 1))))))))))) ty
  where ty = TyArrow TyInt (TyArrow TyInt TyInt)

toUnary :: Int -> Term
toUnary n
  | n == 0 = Zero
  | otherwise = Succ (toUnary (n-1))

toNumber :: Term -> Int
toNumber Zero = 0
toNumber (Succ t) = 1 + toNumber t
toNumber _ = 0

add :: Int -> Int -> Int
add a b = toNumber (eval program)
  where program = App (App adder (toUnary a)) (toUnary b)

main :: Effect Unit
main = do
  logShow (infer adder)
  logShow (add 100 103)
