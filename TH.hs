{- Template Haskell re-design with GADTs -}

{-# LANGUAGE DataKinds, GADTs, StandaloneDeriving, KindSignatures,
             FlexibleInstances, DeriveGeneric, AutoDeriveTypeable #-}

module TH where

import           Data.Word
import           Data.Data            ( Data, Typeable, mkConstr, mkDataType )
import qualified Data.Data    as Data
import           GHC.Generics         ( Generic )

-- Let's pretend that Names and Modules are just Strings:
type Name   = String
type Module = String

-----------------------------------------------------
--
--      The main syntax data types
--
-----------------------------------------------------

data Fixity          = Fixity Int FixityDirection
    deriving( Eq, Show, Data, Typeable, Generic )
data FixityDirection = InfixL | InfixR | InfixN
    deriving( Eq, Show, Data, Typeable, Generic )

data Lit = CharL Char
         | StringL String
         | IntegerL Integer     -- ^ Used for overloaded and non-overloaded
                                -- literals. We don't have a good way to
                                -- represent non-overloaded literals at
                                -- the moment. Maybe that doesn't matter?
         | RationalL Rational   -- Ditto
         | IntPrimL Integer
         | WordPrimL Integer
         | FloatPrimL Rational
         | DoublePrimL Rational
         | StringPrimL [Word8]  -- ^ A primitive C-style string, type Addr#
    deriving( Show, Eq, Data, Typeable, Generic )

    -- We could add Int, Float, Double etc, as we do in HsLit,
    -- but that could complicate the
    -- suppposedly-simple TH.Syntax literal type

-- | Pattern in Haskell given in @{}@
data Pat
  = LitP Lit                      -- ^ @{ 5 or 'c' }@
  | VarP Name                     -- ^ @{ x }@
  | TupP [Pat]                    -- ^ @{ (p1,p2) }@
  | UnboxedTupP [Pat]             -- ^ @{ (# p1,p2 #) }@
  | ConP Name [Pat]               -- ^ @data T1 = C1 t1 t2; {C1 p1 p1} = e@
  | InfixP Pat Name Pat           -- ^ @foo ({x :+ y}) = e@
  | UInfixP Pat Name Pat          -- ^ @foo ({x :+ y}) = e@
                                  --
                                  -- See "Language.Haskell.TH.Syntax#infix"
  | ParensP Pat                   -- ^ @{(p)}@
                                  --
                                  -- See "Language.Haskell.TH.Syntax#infix"
  | TildeP Pat                    -- ^ @{ ~p }@
  | BangP Pat                     -- ^ @{ !p }@
  | AsP Name Pat                  -- ^ @{ x \@ p }@
  | WildP                         -- ^ @{ _ }@
  | RecP Name [FieldPat]          -- ^ @f (Pt { pointx = x }) = g x@
  | ListP [ Pat ]                 -- ^ @{ [1,2,3] }@
  | SigP Pat Type                 -- ^ @{ p :: t }@
  | ViewP Exp Pat                 -- ^ @{ e -> p }@
  deriving( Show, Eq, Data, Typeable, Generic )

type FieldPat = (Name,Pat)

data Match = Match Pat Body [LetDec] -- ^ @case e of { pat -> body where decs }@
    deriving( Show, Eq, Data, Typeable, Generic )
data Clause = Clause [Pat] Body [LetDec]
                                  -- ^ @f { p1 p2 = body where decs }@
    deriving( Show, Eq, Data, Typeable, Generic )

data Exp
  = VarE Name                          -- ^ @{ x }@
  | ConE Name                          -- ^ @data T1 = C1 t1 t2; p = {C1} e1 e2  @
  | LitE Lit                           -- ^ @{ 5 or 'c'}@
  | AppE Exp Exp                       -- ^ @{ f x }@

  | InfixE (Maybe Exp) Exp (Maybe Exp) -- ^ @{x + y} or {(x+)} or {(+ x)} or {(+)}@
  | UInfixE Exp Exp Exp                -- ^ @{x + y}@
                                       --
                                       -- See "Language.Haskell.TH.Syntax#infix"
  | ParensE Exp                        -- ^ @{ (e) }@
                                       --
                                       -- See "Language.Haskell.TH.Syntax#infix"
  | LamE [Pat] Exp                     -- ^ @{ \ p1 p2 -> e }@
  | LamCaseE [Match]                   -- ^ @{ \case m1; m2 }@
  | TupE [Exp]                         -- ^ @{ (e1,e2) }  @
  | UnboxedTupE [Exp]                  -- ^ @{ (# e1,e2 #) }  @
  | CondE Exp Exp Exp                  -- ^ @{ if e1 then e2 else e3 }@
  | MultiIfE [(Guard, Exp)]            -- ^ @{ if | g1 -> e1 | g2 -> e2 }@
  | LetE [LetDec] Exp                  -- ^ @{ let x=e1;   y=e2 in e3 }@
  | CaseE Exp [Match]                  -- ^ @{ case e of m1; m2 }@
  | DoE [Stmt]                         -- ^ @{ do { p <- e1; e2 }  }@
  | CompE [Stmt]                       -- ^ @{ [ (x,y) | x <- xs, y <- ys ] }@
      --
      -- The result expression of the comprehension is
      -- the /last/ of the @'Stmt'@s, and should be a 'NoBindS'.
      --
      -- E.g. translation:
      --
      -- > [ f x | x <- xs ]
      --
      -- > CompE [BindS (VarP x) (VarE xs), NoBindS (AppE (VarE f) (VarE x))]

  | ArithSeqE Range                    -- ^ @{ [ 1 ,2 .. 10 ] }@
  | ListE [ Exp ]                      -- ^ @{ [1,2,3] }@
  | SigE Exp Type                      -- ^ @{ e :: t }@
  | RecConE Name [FieldExp]            -- ^ @{ T { x = y, z = w } }@
  | RecUpdE Exp [FieldExp]             -- ^ @{ (f x) { z = w } }@
  deriving( Show, Eq, Data, Typeable, Generic )

type FieldExp = (Name,Exp)

-- Omitted: implicit parameters

data Body
  = GuardedB [(Guard,Exp)]   -- ^ @f p { | e1 = e2
                                 --      | e3 = e4 }
                                 -- where ds@
  | NormalB Exp              -- ^ @f p { = e } where ds@
  deriving( Show, Eq, Data, Typeable, Generic )

data Guard
  = NormalG Exp -- ^ @f x { | odd x } = x@
  | PatG [Stmt] -- ^ @f x { | Just y <- x, Just z <- y } = z@
  deriving( Show, Eq, Data, Typeable, Generic )

data Stmt
  = BindS Pat Exp
  | LetS [ LetDec ]
  | NoBindS Exp
  | ParS [[Stmt]]
  deriving( Show, Eq, Data, Typeable, Generic )

data Range = FromR Exp | FromThenR Exp Exp
           | FromToR Exp Exp | FromThenToR Exp Exp Exp
          deriving( Show, Eq, Data, Typeable, Generic )

data InTopLevel = YesInTopLevel | NoInTopLevel  deriving Typeable
data InClass    = YesInClass    | NoInClass     deriving Typeable
data InInstance = YesInInstance | NoInInstance  deriving Typeable
data InLet      = YesInLet      | NoInLet       deriving Typeable

type TopLevelDec = Dec (DC YesInTopLevel NoInClass  NoInInstance  NoInLet)
type ClassDec    = Dec (DC NoInTopLevel  YesInClass NoInInstance  NoInLet)
type InstanceDec = Dec (DC NoInTopLevel  NoInClass  YesInInstance NoInLet)
type LetDec      = Dec (DC NoInTopLevel  NoInClass  NoInInstance  YesInLet)

data DecContext = DC InTopLevel InClass InInstance InLet
  deriving Typeable

data Dec :: DecContext -> * where
  FunD :: Name -> [Clause]
       -> Dec (DC top cls inst lt)
    -- ^ @{ f p1 p2 = b where decs }@
           
  ValD :: Pat -> Body -> [LetDec]
       -> Dec (DC top cls inst lt)
    -- ^ @{ p = b where decs }@
           
  DataD :: Cxt -> Name -> [TyVarBndr] -> [Con] -> [Name]
        -> Dec (DC top NoInClass NoInInstance NoInLet)
    -- ^ @{ data Cxt x => T x = A x | B (T x)
    --       deriving (Z,W)}@
           
  NewtypeD :: Cxt -> Name -> [TyVarBndr] -> Con -> [Name]
           -> Dec (DC top NoInClass NoInInstance NoInLet)
    -- ^ @{ newtype Cxt x => T x = A (B x)
    --       deriving (Z,W)}@
              
  TySynD :: Name -> [TyVarBndr] -> Type
         -> Dec (DC top NoInClass NoInInstance NoInLet)
    -- ^ @{ type T x = (x,x) }@
         
  ClassD :: Cxt -> Name -> [TyVarBndr] -> [FunDep] -> [ClassDec]
         -> Dec (DC top NoInClass NoInInstance NoInLet)
    -- ^ @{ class Eq a => Ord a where ds }@
            
  InstanceD :: Cxt -> Type -> [InstanceDec]
            -> Dec (DC top NoInClass NoInInstance NoInLet)
    -- ^ @{ instance Show w => Show [w] where ds }@
               
  SigD :: Name -> Type -> Dec (DC top cls inst lt)
    -- ^ @{ length :: [a] -> Int }@
          
  ForeignD :: Foreign
           -> Dec (DC top NoInClass NoInInstance NoInLet)
    -- ^ @{ foreign import ... }
    -- { foreign export ... }@

  InfixD :: Fixity -> Name
         -> Dec (DC top cls NoInInstance lt)
    -- ^ @{ infix 3 foo }@

  -- | pragmas
  PragmaD :: Pragma loc
          -> Dec loc
    -- ^ @{ {\-# INLINE [1] foo #-\} }@

  -- | type families (may also appear in [Dec] of 'ClassD' and 'InstanceD')
  FamilyD :: FamFlavour -> Name -> [TyVarBndr] -> Maybe Kind
          -> Dec (DC top cls NoInInstance NoInLet)
    -- ^ @{ type family T a b c :: * }@

  DataInstD :: Cxt -> Name -> [Type] -> [Con] -> [Name]
            -> Dec (DC top NoInClass inst NoInLet)
    -- ^ @{ data instance Cxt x => T [x] = A x
    --                                | B (T x)
    --       deriving (Z,W)}@
               
  NewtypeInstD :: Cxt -> Name -> [Type] -> Con -> [Name]
               -> Dec (DC top NoInClass inst NoInLet)
    -- ^ @{ newtype instance Cxt x => T [x] = A (B x)
    --       deriving (Z,W)}@
                  
  TySynInstD :: Name -> TySynEqn
             -> Dec (DC top cls inst NoInLet)
    -- ^ @{ type instance ... }@

  ClosedTypeFamilyD :: Name -> [TyVarBndr] -> Maybe Kind -> [TySynEqn]
                    -> Dec (DC top NoInClass NoInInstance NoInLet)
    -- ^ @{ type family F a b :: * where ... }@

  RoleAnnotD :: Name -> [Role]
             -> Dec (DC top NoInClass NoInInstance NoInLet)
    -- ^ @{ type role T nominal representational }@

deriving instance Show (Dec ctxt)
deriving instance Eq (Dec ctxt)
deriving instance Typeable Dec

-- | One equation of a type family instance or closed type family. The
-- arguments are the left-hand-side type patterns and the right-hand-side
-- result.
data TySynEqn = TySynEqn [Type] Type
  deriving( Show, Eq, Data, Typeable, Generic )

data FunDep = FunDep [Name] [Name]
  deriving( Show, Eq, Data, Typeable, Generic )

data FamFlavour = TypeFam | DataFam
  deriving( Show, Eq, Data, Typeable, Generic )

data Foreign = ImportF Callconv Safety String Name Type
             | ExportF Callconv        String Name Type
         deriving( Show, Eq, Data, Typeable, Generic )

data Callconv = CCall | StdCall
          deriving( Show, Eq, Data, Typeable, Generic )

data Safety = Unsafe | Safe | Interruptible
        deriving( Show, Eq, Data, Typeable, Generic )

data Pragma :: DecContext -> * where
  InlineP :: Name -> Inline -> RuleMatch -> Phases
          -> Pragma (DC top cls inst lt)
  SpecialiseP :: Name -> Type -> Maybe Inline -> Phases
              -> Pragma (DC top NoInClass inst lt)
  SpecialiseInstP :: Type -> Pragma (DC NoInTopLevel NoInClass inst NoInLet)
  RuleP :: String -> [RuleBndr] -> Exp -> Exp -> Phases
        -> Pragma (DC top NoInClass NoInInstance NoInLet)
  AnnP :: AnnTarget -> Exp -> Pragma (DC top NoInClass NoInInstance NoInLet)
  LineP :: Int -> String -> Pragma (DC top NoInClass NoInInstance NoInLet)

deriving instance Show (Pragma ctxt)
deriving instance Eq (Pragma ctxt)
deriving instance Typeable Pragma

data Inline = NoInline
            | Inline
            | Inlinable
            deriving (Show, Eq, Data, Typeable)

data RuleMatch = ConLike
               | FunLike
               deriving (Show, Eq, Data, Typeable)

data Phases = AllPhases
            | FromPhase Int
            | BeforePhase Int
            deriving (Show, Eq, Data, Typeable)

data RuleBndr = RuleVar Name
              | TypedRuleVar Name Type
              deriving (Show, Eq, Data, Typeable)

data AnnTarget = ModuleAnnotation
               | TypeAnnotation Name
               | ValueAnnotation Name
              deriving (Show, Eq, Data, Typeable)

type Cxt = [Pred]                 -- ^ @(Eq a, Ord b)@

-- | Since the advent of @ConstraintKinds@, constraints are really just types.
-- Equality constraints use the 'EqualityT' constructor. Constraints may also
-- be tuples of other constraints.
type Pred = Type

data Strict = IsStrict | NotStrict | Unpacked
         deriving( Show, Eq, Data, Typeable, Generic )

data Con = NormalC Name [StrictType]          -- ^ @C Int a@
         | RecC Name [VarStrictType]          -- ^ @C { v :: Int, w :: a }@
         | InfixC StrictType Name StrictType  -- ^ @Int :+ a@
         | ForallC [TyVarBndr] Cxt Con        -- ^ @forall a. Eq a => C [a]@
         deriving( Show, Eq, Data, Typeable, Generic )

type StrictType = (Strict, Type)
type VarStrictType = (Name, Strict, Type)

data Type = ForallT [TyVarBndr] Cxt Type  -- ^ @forall \<vars\>. \<ctxt\> -> \<type\>@
          | AppT Type Type                -- ^ @T a b@
          | SigT Type Kind                -- ^ @t :: k@
          | VarT Name                     -- ^ @a@
          | ConT Name                     -- ^ @T@
          | PromotedT Name                -- ^ @'T@
          | TupleT Int                    -- ^ @(,), (,,), etc.@
          | UnboxedTupleT Int             -- ^ @(#,#), (#,,#), etc.@
          | ArrowT                        -- ^ @->@
          | EqualityT                     -- ^ @~@
          | ListT                         -- ^ @[]@
          | PromotedTupleT Int            -- ^ @'(), '(,), '(,,), etc.@
          | PromotedNilT                  -- ^ @'[]@
          | PromotedConsT                 -- ^ @(':)@
          | StarT                         -- ^ @*@
          | ConstraintT                   -- ^ @Constraint@
          | LitT TyLit                    -- ^ @0,1,2, etc.@
      deriving( Show, Eq, Data, Typeable, Generic )

data TyVarBndr = PlainTV  Name            -- ^ @a@
               | KindedTV Name Kind       -- ^ @(a :: k)@
      deriving( Show, Eq, Data, Typeable, Generic )

data TyLit = NumTyLit Integer             -- ^ @2@
           | StrTyLit String              -- ^ @"Hello"@
  deriving ( Show, Eq, Data, Typeable, Generic )

-- | Role annotations
data Role = NominalR            -- ^ @nominal@
          | RepresentationalR   -- ^ @representational@
          | PhantomR            -- ^ @phantom@
          | InferR              -- ^ @_@
  deriving( Show, Eq, Data, Typeable, Generic )

-- | Annotation target for reifyAnnotations
data AnnLookup = AnnLookupModule Module
               | AnnLookupName Name
               deriving( Show, Eq, Data, Typeable, Generic )

-- | To avoid duplication between kinds and types, they
-- are defined to be the same. Naturally, you would never
-- have a type be 'StarT' and you would never have a kind
-- be 'SigT', but many of the other constructors are shared.
-- Note that the kind @Bool@ is denoted with 'ConT', not
-- 'PromotedT'. Similarly, tuple kinds are made with 'TupleT',
-- not 'PromotedTupleT'.

type Kind = Type

-------------------------------------------------------------
-- Hand-written Data instances for GADTs
-------------------------------------------------------------

instance (Typeable top, Typeable cls, Typeable inst, Typeable lt)
           => Data (Dec (DC top cls inst lt)) where
  gfoldl k z (FunD a b) = z FunD `k` a `k` b
  gfoldl k z (ValD a b c) = z ValD `k` a `k` b `k` c
  gfoldl k z (DataD a b c d e) = z DataD `k` a `k` b `k` c `k` d `k` e
  gfoldl k z (NewtypeD a b c d e) = z NewtypeD `k` a `k` b `k` c `k` d `k` e
  gfoldl k z (TySynD a b c) = z TySynD `k` a `k` b `k` c
  gfoldl k z (ClassD a b c d e) = z ClassD `k` a `k` b `k` c `k` d `k` e
  gfoldl k z (InstanceD a b c) = z InstanceD `k` a `k` b `k` c
  gfoldl k z (SigD a b) = z SigD `k` a `k` b
  gfoldl k z (ForeignD a) = z ForeignD `k` a
  gfoldl k z (InfixD a b) = z InfixD `k` a `k` b
  gfoldl k z (PragmaD a) = z PragmaD `k` a
  gfoldl k z (FamilyD a b c d) = z FamilyD `k` a `k` b `k` c `k` d
  gfoldl k z (DataInstD a b c d e) = z DataInstD `k` a `k` b `k` c `k` d `k` e
  gfoldl k z (NewtypeInstD a b c d e) = z NewtypeInstD `k` a `k` b `k` c `k` d `k` e
  gfoldl k z (TySynInstD a b) = z TySynInstD `k` a `k` b
  gfoldl k z (ClosedTypeFamilyD a b c d) = z ClosedTypeFamilyD `k` a `k` b `k` c `k` d
  gfoldl k z (RoleAnnotD a b) = z RoleAnnotD `k` a `k` b

  gunfold = error "Cannot gunfold the GADT \"Dec\""
  
  toConstr (FunD {}) = con_FunD
  toConstr (ValD {}) = con_ValD
  toConstr (DataD {}) = con_DataD
  toConstr (NewtypeD {}) = con_NewtypeD
  toConstr (TySynD {}) = con_TySynD
  toConstr (ClassD {}) = con_ClassD
  toConstr (InstanceD {}) = con_InstanceD
  toConstr (SigD {}) = con_SigD
  toConstr (ForeignD {}) = con_ForeignD
  toConstr (InfixD {}) = con_InfixD
  toConstr (PragmaD {}) = con_PragmaD
  toConstr (FamilyD {}) = con_FamilyD
  toConstr (DataInstD {}) = con_DataInstD
  toConstr (NewtypeInstD {}) = con_NewtypeInstD
  toConstr (TySynInstD {}) = con_TySynInstD
  toConstr (ClosedTypeFamilyD {}) = con_ClosedTypeFamilyD
  toConstr (RoleAnnotD {}) = con_RoleAnnotD

  dataTypeOf _ = ty_Dec

con_FunD = mkConstr ty_Dec "FunD" [] Data.Prefix
con_ValD = mkConstr ty_Dec "ValD" [] Data.Prefix
con_DataD = mkConstr ty_Dec "DataD" [] Data.Prefix
con_NewtypeD = mkConstr ty_Dec "NewtypeD" [] Data.Prefix
con_TySynD = mkConstr ty_Dec "TySynD" [] Data.Prefix
con_ClassD = mkConstr ty_Dec "ClassD" [] Data.Prefix
con_InstanceD = mkConstr ty_Dec "InstanceD" [] Data.Prefix
con_SigD = mkConstr ty_Dec "SigD" [] Data.Prefix
con_ForeignD = mkConstr ty_Dec "ForeignD" [] Data.Prefix
con_InfixD = mkConstr ty_Dec "InfixD" [] Data.Prefix
con_PragmaD = mkConstr ty_Dec "PragmaD" [] Data.Prefix
con_FamilyD = mkConstr ty_Dec "FamilyD" [] Data.Prefix
con_DataInstD = mkConstr ty_Dec "DataInstD" [] Data.Prefix
con_NewtypeInstD = mkConstr ty_Dec "NewtypeInstD" [] Data.Prefix
con_TySynInstD = mkConstr ty_Dec "TySynInstD" [] Data.Prefix
con_ClosedTypeFamilyD = mkConstr ty_Dec "ClosedTypeFamilyD" [] Data.Prefix
con_RoleAnnotD = mkConstr ty_Dec "RoleAnnotD" [] Data.Prefix
ty_Dec = mkDataType "Language.Haskell.TH.Syntax.Dec"
  [ con_FunD, con_ValD, con_DataD, con_NewtypeD, con_TySynD, con_ClassD
  , con_InstanceD, con_SigD, con_ForeignD, con_InfixD, con_PragmaD
  , con_FamilyD, con_DataInstD, con_NewtypeInstD, con_TySynInstD
  , con_ClosedTypeFamilyD, con_RoleAnnotD
 ]


instance (Typeable top, Typeable cls, Typeable inst, Typeable lt)
           => Data (Pragma (DC top cls inst lt)) where
  gfoldl k z (InlineP a b c d) = z InlineP `k` a `k` b `k` c `k` d
  gfoldl k z (SpecialiseP a b c d) = z SpecialiseP `k` a `k` b `k` c `k` d
  gfoldl k z (SpecialiseInstP a) = z SpecialiseInstP `k` a
  gfoldl k z (RuleP a b c d e) = z RuleP `k` a `k` b `k` c `k` d `k` e
  gfoldl k z (AnnP a b) = z AnnP `k` a `k` b
  gfoldl k z (LineP a b) = z LineP `k` a `k` b

  gunfold = error "Cannot gunfold the GADT \"Pragma\""
    
  toConstr (InlineP {}) = con_InlineP
  toConstr (SpecialiseP {}) = con_SpecialiseP
  toConstr (SpecialiseInstP {}) = con_SpecialiseInstP
  toConstr (RuleP {}) = con_RuleP
  toConstr (AnnP {}) = con_AnnP
  toConstr (LineP {}) = con_LineP

  dataTypeOf _ = ty_Pragma

con_InlineP = mkConstr ty_Pragma "InlineP" [] Data.Prefix
con_SpecialiseP = mkConstr ty_Pragma "SpecialiseP" [] Data.Prefix
con_SpecialiseInstP = mkConstr ty_Pragma "SpecialiseInstP" [] Data.Prefix
con_RuleP = mkConstr ty_Pragma "RuleP" [] Data.Prefix
con_AnnP = mkConstr ty_Pragma "AnnP" [] Data.Prefix
con_LineP = mkConstr ty_Pragma "LineP" [] Data.Prefix
ty_Pragma = mkDataType "Language.Haskell.TH.Syntax.Pragma" [con_InlineP, con_SpecialiseP, con_SpecialiseInstP, con_RuleP, con_AnnP, con_LineP]
