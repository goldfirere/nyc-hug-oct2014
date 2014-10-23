{- Client code that uses the TH GADTs.
   Copyright (c) 2014 Richard Eisenberg
  -}

{-# LANGUAGE ViewPatterns, GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module UseTH where

import qualified Data.Set      as Set
import           Data.Monoid
import           Data.Foldable

import           Language.Haskell.TH
type LetDec = Dec

allNamesBoundExp :: Exp -> Set.Set Name
allNamesBoundExp = go
  where
    go (AppE e1 e2)          = foldMap go [e1, e2]
    go (InfixE m_e1 e2 m_e3) = foldMap go m_e1 <> go e2 <> foldMap go m_e3
    go (UInfixE e1 e2 e3)    = foldMap go [e1, e2, e3]
    go (ParensE e)           = go e
    go (LamE pats e)         = foldMap allNamesBoundPat pats <> go e
    go (LamCaseE matches)    = foldMap allNamesBoundMatch matches
    go (TupE es)             = foldMap go es
    go (UnboxedTupE es)      = foldMap go es
    go (CondE e1 e2 e3)      = foldMap go [e1, e2, e3]
    go (MultiIfE (unzip -> (guards, es)))
                             = foldMap allNamesBoundGuard guards
                            <> foldMap go es
    go (LetE decs e)         = foldMap allNamesBoundLetDec decs <> go e
    go (CaseE e matches)     = go e <> foldMap allNamesBoundMatch matches
    go (DoE stmts)           = foldMap allNamesBoundStmt stmts
    go (CompE stmts)         = foldMap allNamesBoundStmt stmts
    go (ArithSeqE range)     = allNamesBoundRange range
    go (ListE es)            = foldMap go es
    go (SigE e _)            = go e
    go (RecConE _ field_es)  = foldMap (go . snd) field_es
    go (RecUpdE e field_es)  = go e <> foldMap (go . snd) field_es
    go _                     = Set.empty

allNamesBoundMatch :: Match -> Set.Set Name
allNamesBoundMatch (Match pat body decs) = allNamesBoundPat pat
                                        <> allNamesBoundBody body
                                        <> foldMap allNamesBoundLetDec decs

allNamesBoundPat :: Pat -> Set.Set Name
allNamesBoundPat = go
  where
    go (VarP n)            = Set.singleton n
    go (TupP ps)           = foldMap go ps
    go (UnboxedTupP ps)    = foldMap go ps
    go (ConP _ ps)         = foldMap go ps
    go (InfixP p1 _ p2)    = foldMap go [p1, p2]
    go (UInfixP p1 _ p2)   = foldMap go [p1, p2]
    go (ParensP p)         = go p
    go (TildeP p)          = go p
    go (BangP p)           = go p
    go (AsP n p)           = Set.singleton n <> go p
    go (RecP _ field_pats) = foldMap (go . snd) field_pats
    go (ListP ps)          = foldMap go ps
    go (SigP p _)          = go p
    go (ViewP e p)         = allNamesBoundExp e <> go p
    go _                   = Set.empty

allNamesBoundGuard :: Guard -> Set.Set Name
allNamesBoundGuard (NormalG e)  = allNamesBoundExp e
allNamesBoundGuard (PatG stmts) = foldMap allNamesBoundStmt stmts

allNamesBoundLetDec :: LetDec -> Set.Set Name
allNamesBoundLetDec = go
  where
    go (FunD n clauses)   = Set.singleton n
                         <> foldMap allNamesBoundClause clauses
    go (ValD p body decs) = allNamesBoundPat p <> allNamesBoundBody body
                         <> foldMap go decs
    go (SigD {})          = Set.empty
    go (InfixD {})        = Set.empty
    go (PragmaD {})       = Set.empty
    
allNamesBoundStmt :: Stmt -> Set.Set Name
allNamesBoundStmt = go
  where
    go (BindS p e)   = allNamesBoundPat p <> allNamesBoundExp e
    go (LetS decs)   = foldMap allNamesBoundLetDec decs
    go (NoBindS e)   = allNamesBoundExp e
    go (ParS stmtss) = foldMap (foldMap allNamesBoundStmt) stmtss

allNamesBoundRange :: Range -> Set.Set Name
allNamesBoundRange range = foldMap allNamesBoundExp (get_exps range)
  where get_exps (FromR e)              = [e]
        get_exps (FromThenR e1 e2)      = [e1, e2]
        get_exps (FromToR e1 e2)        = [e1, e2]
        get_exps (FromThenToR e1 e2 e3) = [e1, e2, e3]

allNamesBoundBody :: Body -> Set.Set Name
allNamesBoundBody (GuardedB (unzip -> (guards, es)))
  = foldMap allNamesBoundGuard guards <> foldMap allNamesBoundExp es
allNamesBoundBody (NormalB e)
  = allNamesBoundExp e

allNamesBoundClause :: Clause -> Set.Set Name
allNamesBoundClause (Clause pats body decs)
  = foldMap allNamesBoundPat pats <> allNamesBoundBody body
 <> foldMap allNamesBoundLetDec decs
