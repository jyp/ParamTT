{-# LANGUAGE PackageImports, TypeSynonymInstances,
             FlexibleInstances, GADTs, TupleSections,
             GeneralizedNewtypeDeriving, OverloadedStrings,
             RankNTypes, ImpredicativeTypes, TypeOperators, ViewPatterns, ScopedTypeVariables, DeriveFunctor #-}

module TC where

import TT
import Prelude hiding (length,pi)
import Control.Monad.Error hiding (lift)
import Control.Monad.Writer hiding (lift)
import Data.Functor.Identity
import Control.Applicative
type Doc = String
newtype Result a = Result (
  ((ErrorT (Doc)) 
  (Writer [Doc])) a)
 deriving (Functor, Applicative, Monad, MonadError Doc, MonadWriter [Doc])


type Ctx = [(String,Val)]

throw :: Term -> Doc -> Result b
throw term msg = throwError msg

convertible :: Val -> Val -> Bool
convertible = conv $ map show [1..]

tc :: Ctx -> Term -> Val -> Result Val
tc ctx a0 aTy0 = do
 case (a0,aTy0) of
  (TLam x t, Pi a b) ->
    tc ((x,a):ctx) t (b `app` Var x)
  (TILam i x t, Pi a b) ->
    tc ((x,cpi (\j -> ceval i j a)):ctx) t (b `app` (Var x `capp` CVar i))
  (TCPair a b,CPi ty) -> do
    a' <- tc ctx a (face ty)
    tc ctx b (ty `ni` a')
  (TCLam i t, CPi b) -> do
    tc ctx t (b `capp` CVar i)
  (TPsi f, Ni _ a) -> do
    tc ctx f (a --> U)
  _ -> do aTy1 <- ti ctx a0
          unless (convertible aTy0 aTy1) $
            throw a0 "type mismatch"
          return undefined
 return  $ eval a0 []

(-->) :: Val -> Val -> Val
a --> b = Pi a (Lam $ \_ -> b)

cpi :: (CVal -> Val) -> Val
cpi = CPi . CLam 

ti :: Ctx -> Term -> Result Val
ti ctx t0 = let ev x = eval x [] in case t0 of
    TU -> return U
    TPi a b -> do
      a' <- tc ctx a U
      tc ctx b (a' --> U)
      return U
    TCPi t -> do
      tc ctx t $ cpi $ \_ -> U
      return U
    TNi t a -> do
      t' <- tc ctx t $ cpi $ \_ -> U
      tc ctx a (face t')
      return U
    TApp t u -> do
      tTy <- ti ctx t
      case tTy of
        Pi a b -> do
          u' <- tc ctx u a
          return (b `app` u')
    TVar x -> case lookup x ctx of
      Just xTy -> return xTy
    TCApp t i -> do
      tTy <- ti ctx t
      case tTy of
        CPi b -> do
          return (b `capp` i)
    TParam t -> do
      tTy <- ti ctx t
      case tTy of
        CPi b -> do
          return (b `ni` face (ev t))
