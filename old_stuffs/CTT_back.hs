{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module CTT_back where

import Control.Applicative
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum)
import Control.Monad.State
import Control.Monad.RWS hiding (Sum)
import Data.List
import Data.Maybe
import Data.Map (Map,(!),filterWithKey,elems,toList)
import qualified Data.Map as Map
-- import Text.PrettyPrint as PP
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString(..))
import Data.Text (Text)
import qualified Data.Text as T

import Connections hiding (showSystem)

import System.Console.ANSI

import Pretty
import Words
import Exts.ExtPrec hiding (parens)
import Rendering.RenderConsole

--------------------------------------------------------------------------------
-- | Terms

data Loc = Loc { locFile :: String
               , locPos  :: (Int,Int) }
  deriving Eq

type Ident  = String
type LIdent = String

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Ident,Ter)]

data Label = OLabel LIdent Tele -- Object label
           | PLabel LIdent Tele [Name] (System Ter) -- Path label
  deriving (Eq)
  --deriving (Eq,Show)

-- OBranch of the form: c x1 .. xn -> e
-- PBranch of the form: c x1 .. xn i1 .. im -> e
data Branch = OBranch LIdent [Ident] Ter
            | PBranch LIdent [Ident] [Name] Ter
  deriving (Eq)
  --deriving (Eq,Show)

-- Declarations: x : A = e
-- A group of mutual declarations is identified by its location. It is used to
-- speed up the Eq instance for Ctxt.
type Decl  = (Ident,(Ter,Ter))
data Decls = MutualDecls Loc [Decl]
           | OpaqueDecl Ident
           | TransparentDecl Ident
           | TransparentAllDecl
           deriving Eq

declIdents :: [Decl] -> [Ident]
declIdents decls = [ x | (x,_) <- decls ]

declTers :: [Decl] -> [Ter]
declTers decls = [ d | (_,(_,d)) <- decls ]

declTele :: [Decl] -> Tele
declTele decls = [ (x,t) | (x,(t,_)) <- decls ]

declDefs :: [Decl] -> [(Ident,Ter)]
declDefs decls = [ (x,d) | (x,(_,d)) <- decls ]

labelTele :: Label -> (LIdent,Tele)
labelTele (OLabel c ts) = (c,ts)
labelTele (PLabel c ts _ _) = (c,ts)

labelName :: Label -> LIdent
labelName = fst . labelTele

labelTeles :: [Label] -> [(LIdent,Tele)]
labelTeles = map labelTele

lookupLabel :: LIdent -> [Label] -> Maybe Tele
lookupLabel x xs = lookup x (labelTeles xs)

lookupPLabel :: LIdent -> [Label] -> Maybe (Tele,[Name],System Ter)
lookupPLabel x xs = listToMaybe [ (ts,is,es) | PLabel y ts is es <- xs, x == y ]

branchName :: Branch -> LIdent
branchName (OBranch c _ _) = c
branchName (PBranch c _ _ _) = c

lookupBranch :: LIdent -> [Branch] -> Maybe Branch
lookupBranch _ []      = Nothing
lookupBranch x (b:brs) = case b of
  OBranch c _ _   | x == c    -> Just b
                  | otherwise -> lookupBranch x brs
  PBranch c _ _ _ | x == c    -> Just b
                  | otherwise -> lookupBranch x brs

-- Terms
data Ter = Pi Ter
         | App Ter Ter
         | Lam Ident Ter Ter
         | Where Ter Decls
         | Var Ident
         | U
           -- Sigma types:
         | Sigma Ter
         | Pair Ter Ter
         | Fst Ter
         | Snd Ter
           -- constructor c Ms
         | Con LIdent [Ter]
         | PCon LIdent Ter [Ter] [Formula] -- c A ts phis (A is the data type)
           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Ident Loc Ter [Branch]
           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Loc Ident [Label] -- TODO: should only contain OLabels
         | HSum Loc Ident [Label]
           -- undefined and holes
         | Undef Loc Ter -- Location and type
         | Hole Loc
           -- Path types
         | PathP Ter Ter Ter
         | PLam Name Ter
         | AppFormula Ter Formula
           -- Kan composition and filling
         | Comp Ter Ter (System Ter)
         | Fill Ter Ter (System Ter)
           -- Glue
         | Glue Ter (System Ter)
         | GlueElem Ter (System Ter)
         | UnGlueElem Ter (System Ter)
           -- Id
         | Id Ter Ter Ter
         | IdPair Ter (System Ter)
         | IdJ Ter Ter Ter Ter Ter Ter
  deriving Eq

-- For an expression t, returns (u,ts) where u is no application and t = u ts
unApps :: Ter -> (Ter,[Ter])
unApps = aux []
  where aux :: [Ter] -> Ter -> (Ter,[Ter])
        aux acc (App r s) = aux (s:acc) r
        aux acc t         = (t,acc)

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Values

data Val = VU
         | Ter Ter Env
         | VPi Val Val
         | VSigma Val Val
         | VPair Val Val
         | VCon LIdent [Val]
         | VPCon LIdent Val [Val] [Formula]

           -- Path values
         | VPathP Val Val Val
         | VPLam Name Val
         | VComp Val Val (System Val)

           -- Glue values
         | VGlue Val (System Val)
         | VGlueElem Val (System Val)
         | VUnGlueElem Val (System Val)

           -- Composition in the universe
         | VCompU Val (System Val)

           -- Composition for HITs; the type is constant
         | VHComp Val Val (System Val)

           -- Id
         | VId Val Val Val
         | VIdPair Val (System Val)

           -- Neutral values:
         | VVar Ident Val
         | VOpaque Ident Val
         | VFst Val
         | VSnd Val
         | VSplit Val Val
         | VApp Val Val
         | VAppFormula Val Formula
         | VLam Ident Val Val
         | VUnGlueElemU Val Val (System Val)
         | VIdJ Val Val Val Val Val Val
  deriving Eq

isNeutral :: Val -> Bool
isNeutral v = case v of
  Ter Undef{} _  -> True
  Ter Hole{} _   -> True
  VVar{}         -> True
  VOpaque{}      -> True
  VComp{}        -> True
  VFst{}         -> True
  VSnd{}         -> True
  VSplit{}       -> True
  VApp{}         -> True
  VAppFormula{}  -> True
  VUnGlueElemU{} -> True
  VUnGlueElem{}  -> True
  VIdJ{}         -> True
  _              -> False

isNeutralSystem :: System Val -> Bool
isNeutralSystem = any isNeutral . elems

-- isNeutralPath :: Val -> Bool
-- isNeutralPath (VPath _ v) = isNeutral v
-- isNeutralPath _ = True

mkVar :: Int -> String -> Val -> Val
mkVar k x = VVar (x ++ show k)

mkVarNice :: [String] -> String -> Val -> Val
mkVarNice xs x = VVar (head (ys \\ xs))
  where ys = x:map (\n -> x ++ show n) [0..]

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " -- ++ show v

isCon :: Val -> Bool
isCon VCon{} = True
isCon _      = False

-- Constant path: <_> v
constPath :: Val -> Val
constPath = VPLam (Name "_")


--------------------------------------------------------------------------------
-- | Environments

data Ctxt = Empty
          | Upd Ident Ctxt
          | Sub Name Ctxt
          | Def Loc [Decl] Ctxt
  -- deriving (Pretty)

instance Eq Ctxt where
    c == d = case (c, d) of
        (Empty, Empty)              -> True
        (Upd x c', Upd y d')        -> x == y && c' == d'
        (Sub i c', Sub j d')        -> i == j && c' == d'
        (Def m xs c', Def n ys d')  -> (m == n || xs == ys) && c' == d'
            -- Invariant: if two declaration groups come from the same
            -- location, they are equal and their contents are not compared.
        _                           -> False

-- The Idents and Names in the Ctxt refer to the elements in the two
-- lists. This is more efficient because acting on an environment now
-- only need to affect the lists and not the whole context.
-- The last list is the list of opaque names
type Env = (Ctxt,[Val],[Formula],Nameless (Set Ident))

emptyEnv :: Env
emptyEnv = (Empty,[],[],Nameless Set.empty)

def :: Decls -> Env -> Env
def (MutualDecls m ds) (rho,vs,fs,Nameless os) = (Def m ds rho,vs,fs,Nameless (os Set.\\ Set.fromList (declIdents ds)))
def (OpaqueDecl n) (rho,vs,fs,Nameless os) = (rho,vs,fs,Nameless (Set.insert n os))
def (TransparentDecl n) (rho,vs,fs,Nameless os) = (rho,vs,fs,Nameless (Set.delete n os))
def TransparentAllDecl (rho,vs,fs,Nameless os) = (rho,vs,fs,Nameless Set.empty)

defWhere :: Decls -> Env -> Env
defWhere (MutualDecls m ds) (rho,vs,fs,Nameless os) = (Def m ds rho,vs,fs,Nameless (os Set.\\ Set.fromList (declIdents ds)))
defWhere (OpaqueDecl _) rho = rho
defWhere (TransparentDecl _) rho = rho
defWhere TransparentAllDecl rho = rho

sub :: (Name,Formula) -> Env -> Env
sub (i,phi) (rho,vs,fs,os) = (Sub i rho,vs,phi:fs,os)

upd :: (Ident,Val) -> Env -> Env
upd (x,v) (rho,vs,fs,Nameless os) = (Upd x rho,v:vs,fs,Nameless (Set.delete x os))

upds :: [(Ident,Val)] -> Env -> Env
upds xus rho = foldl (flip upd) rho xus

updsTele :: Tele -> [Val] -> Env -> Env
updsTele tele vs = upds (zip (map fst tele) vs)

subs :: [(Name,Formula)] -> Env -> Env
subs iphis rho = foldl (flip sub) rho iphis

mapEnv :: (Val -> Val) -> (Formula -> Formula) -> Env -> Env
mapEnv f g (rho,vs,fs,os) = (rho,map f vs,map g fs,os)

valAndFormulaOfEnv :: Env -> ([Val],[Formula])
valAndFormulaOfEnv (_,vs,fs,_) = (vs,fs)

valOfEnv :: Env -> [Val]
valOfEnv = fst . valAndFormulaOfEnv

formulaOfEnv :: Env -> [Formula]
formulaOfEnv = snd . valAndFormulaOfEnv

domainEnv :: Env -> [Name]
domainEnv (rho,_,_,_) = domCtxt rho
  where domCtxt rho = case rho of
          Empty      -> []
          Upd _ e    -> domCtxt e
          Def _ ts e -> domCtxt e
          Sub i e    -> i : domCtxt e

-- Extract the context from the environment, used when printing holes
  {-
contextOfEnv :: Env -> [String]
contextOfEnv rho = case rho of
  (Empty,_,_,_)               -> []
  (Upd x e,VVar n t:vs,fs,os) -> (n ++ " : " ++ show t) : contextOfEnv (e,vs,fs,os)
  (Upd x e,v:vs,fs,os)        -> (x ++ " = " ++ show v) : contextOfEnv (e,vs,fs,os)
  (Def _ _ e,vs,fs,os)        -> contextOfEnv (e,vs,fs,os)
  (Sub i e,vs,phi:fs,os)      -> (show i ++ " = " ++ show phi) : contextOfEnv (e,vs,fs,os)
-}
contextOfEnv :: Env -> [Doc]
contextOfEnv rho = case rho of
  (Empty,_,_,_)               -> []
  (Upd x e,VVar n t:vs,fs,os) -> ((text (T.pack (n ++ " : "))) >> (ppVal t)) : contextOfEnv (e,vs,fs,os)
  (Upd x e,v:vs,fs,os)        -> ((text (T.pack (x ++ " = "))) >> (ppVal v)) : contextOfEnv (e,vs,fs,os)
  (Def _ _ e,vs,fs,os)        -> contextOfEnv (e,vs,fs,os)
  (Sub i e,vs,phi:fs,os)      -> text (T.pack (show i ++ " = " ++ show phi)) : contextOfEnv (e,vs,fs,os)

--------------------------------------------------------------------------------
-- | Pretty printing

data Ann = Class Text | Tooltip Text
  deriving (Eq, Ord, Show)

idAnn :: Ann
idAnn = Class "id"

glueAnn :: Ann
glueAnn = Class "glue"

pathAnn :: Ann
pathAnn = Class "path"

holeAnn :: Ann
holeAnn = Class "hole"

updateColor :: forall ann . StateT [Ann] IO ()
updateColor =
  lift . setSGR =<< mconcat . map toSGR . reverse <$> get

openTag :: Ann -> StateT [Ann] IO ()
openTag ann = modify (ann:) >> updateColor

closeTag :: Ann -> StateT [Ann] IO ()
closeTag _  = modify tail   >> updateColor


renderAnnotation :: Ann -> StateT [Ann] IO () -> StateT [Ann] IO ()
renderAnnotation a o = openTag a >> o >> closeTag a

type TEnv = Map Text Text

tEnv0 :: TEnv
tEnv0 = Map.empty

  {-
env0 :: Monoid fmt => PEnv Int a fmt
env0 = PEnv
  { maxWidth = 80
  , maxRibbon = 60
  , layout = Break
  , failure = CantFail
  , nesting = 0
  , formatting = mempty
  , formatAnn = const mempty
  }

state0 :: PState Int ()
state0 = PState
  { curLine = []
  }
-}

  {-
newtype DocM a = DocM { unDocM :: RWST (PEnv Int Ann ()) (POut Int Ann) (PState Int ()) Maybe a }
  deriving
    ( Functor, Applicative, Monad
    , MonadReader (PEnv Int Ann ()), MonadWriter (POut Int Ann), MonadState (PState Int ()), Alternative
    )
instance MonadPretty Int Ann () DocM
-}
newtype DocM a = DocM { unDocM :: PrecT Ann (RWST (PEnv Int Ann ()) (POut Int Ann) (PState Int ()) (ReaderT TEnv Maybe)) a }
  deriving
    ( Functor, Applicative, Monad, Alternative
    , MonadReader (PEnv Int Ann ()), MonadWriter (POut Int Ann), MonadState (PState Int ())
    , MonadReaderPrec Ann
    )
instance MonadPretty Int Ann () DocM
instance MonadPrettyPrec Int Ann () DocM

instance Measure Int () DocM where
  measure = return . runIdentity . measure

  {-
runDocM :: PEnv Int Ann () -> PState Int () -> DocM a -> Maybe (PState Int (), POut Int Ann, a)
runDocM e s d = (\(a,s',o) -> (s',o,a)) <$> runRWST (unDocM d) e s
-}

runDocM :: PEnv Int Ann () -> PrecEnv Ann -> TEnv -> PState Int () -> DocM a -> Maybe (PState Int (), POut Int Ann, a)
runDocM e pe te s d = (\(a,s',o) -> (s',o,a)) <$> runReaderT (runRWST (runPrecT pe $ unDocM d) e s) te

type Doc = DocM ()

execDoc :: Doc -> POut Int Ann
execDoc d =
  let rM = runDocM env0 precEnv0 tEnv0 state0 d
  in case rM of
    Nothing -> PAtom $ AChunk $ CText "<internal pretty printing error>"
    Just (_, o, ()) -> o

instance IsString Doc where
  fromString = text . fromString

instance Monoid Doc where
  mempty = return ()
  mappend = (>>)

  {-
instance Show Doc where
  show = T.unpack . (render renderAnnotation ). execDoc
-}

class Pretty a where
  pretty :: a -> Doc

instance Pretty Doc where
  pretty = id

instance Pretty Text where
  pretty = text . T.pack . show

instance Pretty Env where
  pretty = ppEnv True

  {-
instance Show Env where
  show = show . pretty
-}

ppEnv :: Bool -> Env -> Doc
ppEnv b e =
  let
    names x  = if b then text x >> space 1 >> equals else mempty
    par x    = if b then parens x else x
    com      = if b then comma else mempty
    ppEnv1 e = case e of
      (Upd x env,u:us,fs,os) ->
        ppEnv1 (env,us,fs,os) >> space 1 >> (names $ T.pack x) >> space 1 >> ppVal1 u >> com
      (Sub i env,us,phi:fs,os) ->
        ppEnv1 (env,us,fs,os) >> space 1 >> (names $ T.pack (show i)) >> space 1 >> (text $ T.pack (show phi)) >> com
      (Def _ _ env,vs,fs,os) -> ppEnv1 (env,vs,fs,os)
      _ -> ppEnv b e
  in case e of
    (Empty,_,_,_)            -> mempty
    (Def _ _ env,vs,fs,os)   -> ppEnv b (env,vs,fs,os)
    (Upd x env,u:us,fs,os)   ->
      par $ ppEnv1 (env,us,fs,os) >> space 1 >> (names $ T.pack x) >> space 1 >> ppVal1 u
    (Sub i env,us,phi:fs,os) ->
      par $ ppEnv1 (env,us,fs,os) >> space 1 >> (names $ T.pack (show i)) >> space 1 >> (text $ T.pack (show phi))

ppFormula :: Formula -> Doc
ppFormula phi = case phi of
  _ :\/: _ -> parens (text $ T.pack (show phi))
  _ :/\: _ -> parens (text $ T.pack (show phi))
  _ -> text $ T.pack $ show phi


ppListSystem :: Pretty a => [(Face , a)] -> Doc
ppListSystem [] = text "[]"
showListSystem ts =
  text "[ " >>
  text (T.pack ("[ " ++ intercalate ", " [ showFace alpha ++ " -> " ++ show u
                           | (alpha,u) <- ts ] ++ " ]")) >>
  text " ]"

ppSystem :: Pretty a => System a -> Doc
ppSystem = ppListSystem . toList

ppTer :: Ter -> Doc
ppTer v = case v of
  U                 -> char 'U'
  App e0 e1         -> grouped $ ppTer e0 >> newline >> ppTer1 e1
  Pi e0             -> grouped $ text "Pi" >> space 1 >> ppTer e0
  Lam x t e         -> grouped $ do
                         char '\\'
                         parens $ do
                           (text $ T.pack x)
                           space 1 >> colon >> space 1
                           ppTer t
                         space 1
                         text "->"
                         nest 2 $ do newline; ppTer e
  Fst e             -> ppTer1 e >> text ".1"
  Snd e             -> ppTer1 e >> text ".2"
  Sigma e0          -> grouped $ text "Sigma" >> space 1 >> ppTer1 e0
  Where e d         -> ppTer e >> newline >> text "where" >> newline >> ppDecls d
  Var x             -> annotate idAnn $ text $ T.pack x
  Con c es          -> (text $ T.pack c) >> space 1 >> ppTers es
  PCon c a es phis  -> grouped $ do
                         text $ T.pack c
                         space 1
                         braces $ ppTer a
                         space 1
                         ppTers es
                         space 1
                         hsep $ map ((char '@' >> space 1 >> ) . ppFormula) phis
  -- PCon c a es phis  -> (text $ T.pack c) >> space 1 >> braces (ppTer a) >> space 1 >> ppTers es >> space 1 >> hsep (map ((char '@' >> space 1 >> ) . ppFormula) phis)
  Split f _ _ _     -> text $ T.pack f
  Sum _ n _         -> text $ T.pack n
  HSum _ n _        -> text $ T.pack n
  Undef{}           -> text "undefined"
  Hole{}            -> annotate holeAnn $ text "?"
  PathP e0 e1 e2    -> annotate pathAnn $ text "PathP" >> space 1 >> ppTers [e0,e1,e2]
  PLam i e          -> char '<' >> (text $ T.pack (show i)) >> char '>' >> space 1 >> ppTer e
  AppFormula e phi  -> ppTer1 e >> space 1 >> char '@' >> space 1 >> ppFormula phi
  Comp e t ts       -> text "comp" >> space 1 >> ppTers [e,t] >> space 1 >> ppSystem ts
  Fill e t ts       -> text "fill" >> space 1 >> ppTers [e,t] >> space 1 >> ppSystem ts
  Glue a ts         -> text "Glue" >> space 1 >> ppTer a >> space 1 >> ppSystem ts
  GlueElem a ts     -> text "glue" >> space 1 >> ppTer a >> space 1 >> ppSystem ts
  UnGlueElem a ts   -> text "unglue" >> space 1 >> ppTer a >> space 1 >> ppSystem ts
  Id a u v          -> grouped $ text "Id" >> space 1 >> ppTers [a,u,v]
  IdPair b ts       -> text "IdC" >> space 1 >> ppTer b >> space 1 >> ppSystem ts
  IdJ a t c d x p   -> grouped $ text "IdJ" >> space 1 >> ppTers [a,t,c,d,x,p]
 
ppTer1 :: Ter -> Doc
ppTer1 t = case t of
  U        -> char 'U'
  Con c [] -> text $ T.pack c
  Var{}    -> ppTer t
  Undef{}  -> ppTer t
  Hole{}   -> ppTer t
  Split{}  -> ppTer t
  Sum{}    -> ppTer t
  HSum{}   -> ppTer t
  Fst{}    -> ppTer t
  Snd{}    -> ppTer t
  _        -> parens (ppTer t)
  

ppTers :: [Ter] -> Doc
ppTers = vsep . map ppTer1

ppDecls :: Decls -> Doc
ppDecls ds = case ds of
  MutualDecls _ defs -> hsep $ punctuate comma [(text $ T.pack x) >> space 1 >> equals >> space 1 >> ppTer d | (x,(_,d)) <- defs]
  OpaqueDecl i -> text "opaque" >> space 1 >> (text $ T.pack i)
  TransparentDecl i -> text "transparent" >> space 1 >> (text $ T.pack i)
  TransparentAllDecl -> text "transparent_all"

instance Pretty Ter where
  pretty = ppTer

  {-
instance Show Ter where
  show = show . pretty 
-}

ppLoc :: Loc -> Doc
ppLoc (Loc name (i,j)) = text $ T.pack (show (i,j) ++ " in " ++ name)

instance Pretty Loc where
  pretty = ppLoc

  {-
instance Show Loc where
  show = show . pretty 
-}

ppVal :: Val -> Doc
ppVal v = case v of
  VU                     -> char 'U'
  Ter t@Sum{} rho        -> ppTer t >> space 1 >> ppEnv False rho 
  Ter t@HSum{} rho       -> ppTer t >> space 1 >> ppEnv False rho
  Ter t@Split{} rho      -> ppTer t >> space 1 >> ppEnv False rho
  Ter t rho              -> ppTer t >> space 1 >> ppEnv True rho 
  VCon c us              -> (text $ T.pack c) >> space 1 >> ppVals us
  VPCon c a us phis      -> (text $ T.pack c) >> space 1 >> braces (ppVal a) >> space 1 >> ppVals us >> hsep (map ((char '@' >> space 1 >>) . ppFormula) phis)
  VHComp v0 v1 vs        -> text "hComp" >> space 1 >> ppVals [v0,v1] >> space 1 >> ppSystem vs
  VPi a l@(VLam x t b)
    | "_" `isPrefixOf` x -> ppVal1 a >> space 1 >> text "->" >> space 1 >> ppVal1 b
    | otherwise          -> char '(' >> ppLam (VPi a l)
  VPi a b                -> text "Pi" >> space 1 >> ppVals [a,b] 
  VPair u v              -> parens (ppVal u >> comma >> ppVal v)
  VSigma u v             -> text "Sigma" >> space 1 >> ppVals [u,v]
  VApp u v               -> ppVal u >> space 1 >> ppVal1 v
  VLam{}                 -> text "\\(" >> ppLam v
  VPLam{}                -> char '<' >> ppPLam v
  VSplit u v             -> ppVal u >> space 1 >> ppVal1 v
  VVar x _               -> text $ T.pack x
  VOpaque x _            -> text $ T.pack x
  VFst u                 -> ppVal1 u >> space 1 >> text ".1"
  VSnd u                 -> ppVal1 u >> space 2 >> text ".2"
  VPathP v0 v1 v2        -> text "PathP" >> space 1 >> ppVals [v0,v1,v2]
  VAppFormula v phi      -> ppVal v >> space 1 >> char '@' >> ppFormula phi
  VComp v0 v1 vs         -> text "comp" >> space 1 >> ppVals [v0,v1] >> space 1 >> ppSystem vs
  VGlue a ts             -> text "Glue" >> space 1 >> ppVal1 a >> space 1 >> ppSystem ts
  VGlueElem a ts         -> text "glue" >> space 1 >> ppVal1 a >> space 1 >> ppSystem ts
  VUnGlueElem a ts       -> text "unglue" >> space 1 >> ppVal1 a >> space 1 >> ppSystem ts
  VUnGlueElemU v b es    -> text "unglue U" >> space 1 >> ppVals [v,b] >> ppSystem es
  VCompU a ts            -> text "comp (<_> U)" >> space 1 >> ppVal1 a >> space 1 >> ppSystem ts
  VId a u v              -> text "Id" >> space 1 >> ppVals [a,u,v]
  VIdPair b ts           -> text "IdC" >> space 1 >> ppVal1 b >> ppSystem ts
  VIdJ a t c d x p       -> text "IdJ" >> space 1 >> ppVals [a,t,c,d,x,p]

ppLam :: Val -> Doc
ppLam e = case e of
  VLam x t a@(VLam _ t' _)
    | t == t'   -> (text $ T.pack x) >> space 1 >> ppLam a
    | otherwise -> (text $ T.pack x) >> space 1 >> colon >> space 1 >> ppVal t >> char ')' >> space 1 >> text "->" >> space 1 >> ppVal a
  VPi _ (VLam x t a@(VPi _ (VLam _ t' _)))
    | t == t'   -> (text $ T.pack x) >> space 1 >> ppLam a
    | otherwise -> (text $ T.pack x) >> space 1 >> colon >> space 1 >> ppVal t >> char ')' >> space 1 >> text "->" >> space 1 >> ppVal a
  VLam x t e ->
    (text $ T.pack x) >> space 1 >> colon >> space 1 >> ppVal t >> char ')' >> space 1 >> text "->" >> space 1 >> ppVal e
  VPi _ (VLam x t e) ->
    (text $ T.pack x) >> colon >> space 1 >> ppVal t >> char ')' >> space 1 >>  text "->" >> space 1 >> ppVal e
  _ -> ppVal e

ppPLam :: Val -> Doc
ppPLam e = case e of
  VPLam i a@VPLam{} -> (text $ T.pack (show i)) >> space 1 >> ppPLam a
  VPLam i a -> (text $ T.pack (show i)) >> char '>' >> space 1 >> ppVal a
  _ -> ppVal e

ppVals :: [Val] -> Doc
ppVals = hsep . map ppVal1

ppVal1 :: Val -> Doc
ppVal1 v = case v of
  VU                -> ppVal v
  VCon c []         -> ppVal v
  VVar{}            -> ppVal v
  VFst{}            -> ppVal v
  VSnd{}            -> ppVal v
  Ter t@Sum{} rho   -> ppTer t >> space 1 >> ppEnv False rho
  Ter t@HSum{} rho  -> ppTer t >> space 1 >> ppEnv False rho
  Ter t@Split{} rho -> ppTer t >> space 1 >> ppEnv False rho
  Ter t rho         -> ppTer t >> space 1 >> ppEnv True rho
  _                 -> parens (ppVal v)

instance Pretty Val where
  pretty = ppVal

  {-
instance Show Val where
  show = show . pretty 
-}

toSGR :: Ann -> [SGR]
toSGR _ = [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]

dumpTer :: Ter -> IO ()
dumpTer = dumpDoc toSGR renderAnnotation . execDoc . pretty

{- 
instance Show Env where
  show = render . showEnv True

showEnv :: Bool -> Env -> Doc
showEnv b e =
  let -- This decides if we should print "x = " or not
      names x = if b then text x <+> equals else PP.empty
      par   x = if b then parens x else x
      com     = if b then comma else PP.empty
      showEnv1 e = case e of
        (Upd x env,u:us,fs,os)   ->
          showEnv1 (env,us,fs,os) <+> names x <+> showVal1 u <> com
        (Sub i env,us,phi:fs,os) ->
          showEnv1 (env,us,fs,os) <+> names (show i) <+> text (show phi) <> com
        (Def _ _ env,vs,fs,os)   -> showEnv1 (env,vs,fs,os)
        _                        -> showEnv b e
  in case e of
    (Empty,_,_,_)            -> PP.empty
    (Def _ _ env,vs,fs,os)   -> showEnv b (env,vs,fs,os)
    (Upd x env,u:us,fs,os)   ->
      par $ showEnv1 (env,us,fs,os) <+> names x <+> showVal1 u
    (Sub i env,us,phi:fs,os) ->
      par $ showEnv1 (env,us,fs,os) <+> names (show i) <+> text (show phi)

instance Show Loc where
  show = render . showLoc

showLoc :: Loc -> Doc
showLoc (Loc name (i,j)) = text (show (i,j) ++ " in " ++ name)

showFormula :: Formula -> Doc
showFormula phi = case phi of
  _ :\/: _ -> parens (text (show phi))
  _ :/\: _ -> parens (text (show phi))
  _ -> text $ show phi

instance Show Ter where
  show = render . showTer

showTer :: Ter -> Doc
showTer v = case v of
  U                  -> char 'U'
  App e0 e1          -> showTer e0 <+> showTer1 e1
  Pi e0              -> text "Pi" <+> showTer e0
  Lam x t e          -> char '\\' <> parens (text x <+> colon <+> showTer t) <+>
                          text "->" <+> showTer e
  Fst e              -> showTer1 e <> text ".1"
  Snd e              -> showTer1 e <> text ".2"
  Sigma e0           -> text "Sigma" <+> showTer1 e0
  Pair e0 e1         -> parens (showTer e0 <> comma <> showTer e1)
  Where e d          -> showTer e <+> text "where" <+> showDecls d
  Var x              -> text x
  Con c es           -> text c <+> showTers es
  PCon c a es phis   -> text c <+> braces (showTer a) <+> showTers es
                        <+> hsep (map ((char '@' <+>) . showFormula) phis)
  Split f _ _ _      -> text f
  Sum _ n _          -> text n
  HSum _ n _         -> text n
  Undef{}            -> text "undefined"
  Hole{}             -> text "?"
  PathP e0 e1 e2     -> text "PathP" <+> showTers [e0,e1,e2]
  PLam i e           -> char '<' <> text (show i) <> char '>' <+> showTer e
  AppFormula e phi   -> showTer1 e <+> char '@' <+> showFormula phi
  Comp e t ts        -> text "comp" <+> showTers [e,t] <+> text (showSystem ts)
  Fill e t ts        -> text "fill" <+> showTers [e,t] <+> text (showSystem ts)
  Glue a ts          -> text "Glue" <+> showTer1 a <+> text (showSystem ts)
  GlueElem a ts      -> text "glue" <+> showTer1 a <+> text (showSystem ts)
  UnGlueElem a ts    -> text "unglue" <+> showTer1 a <+> text (showSystem ts)
  Id a u v           -> text "Id" <+> showTers [a,u,v]
  IdPair b ts        -> text "IdC" <+> showTer1 b <+> text (showSystem ts)
  IdJ a t c d x p    -> text "IdJ" <+> showTers [a,t,c,d,x,p]

showTers :: [Ter] -> Doc
showTers = hsep . map showTer1

showTer1 :: Ter -> Doc
showTer1 t = case t of
  U        -> char 'U'
  Con c [] -> text c
  Var{}    -> showTer t
  Undef{}  -> showTer t
  Hole{}   -> showTer t
  Split{}  -> showTer t
  Sum{}    -> showTer t
  HSum{}   -> showTer t
  Fst{}    -> showTer t
  Snd{}    -> showTer t
  _        -> parens (showTer t)

showDecls :: Decls -> Doc
showDecls (MutualDecls _ defs) =
  hsep $ punctuate comma
  [ text x <+> equals <+> showTer d | (x,(_,d)) <- defs ]
showDecls (OpaqueDecl i) = text "opaque" <+> text i
showDecls (TransparentDecl i) = text "transparent" <+> text i
showDecls TransparentAllDecl = text "transparent_all"

instance Show Val where
  show = render . showVal

showVal :: Val -> Doc
showVal v = case v of
  VU                -> char 'U'
  Ter t@Sum{} rho   -> showTer t <+> showEnv False rho
  Ter t@HSum{} rho  -> showTer t <+> showEnv False rho
  Ter t@Split{} rho -> showTer t <+> showEnv False rho
  Ter t rho         -> showTer1 t <+> showEnv True rho
  VCon c us         -> text c <+> showVals us
  VPCon c a us phis -> text c <+> braces (showVal a) <+> showVals us
                       <+> hsep (map ((char '@' <+>) . showFormula) phis)
  VHComp v0 v1 vs   -> text "hComp" <+> showVals [v0,v1] <+> text (showSystem vs)
  VPi a l@(VLam x t b)
    | "_" `isPrefixOf` x -> showVal1 a <+> text "->" <+> showVal1 b
    | otherwise          -> char '(' <> showLam v
  VPi a b           -> text "Pi" <+> showVals [a,b]
  VPair u v         -> parens (showVal u <> comma <> showVal v)
  VSigma u v        -> text "Sigma" <+> showVals [u,v]
  VApp u v          -> showVal u <+> showVal1 v
  VLam{}            -> text "\\(" <> showLam v
  VPLam{}           -> char '<' <> showPLam v
  VSplit u v        -> showVal u <+> showVal1 v
  VVar x _          -> text x
  VOpaque x _       -> text ('#':x)
  VFst u            -> showVal1 u <> text ".1"
  VSnd u            -> showVal1 u <> text ".2"
  VPathP v0 v1 v2   -> text "PathP" <+> showVals [v0,v1,v2]
  VAppFormula v phi -> showVal v <+> char '@' <+> showFormula phi
  VComp v0 v1 vs    ->
    text "comp" <+> showVals [v0,v1] <+> text (showSystem vs)
  VGlue a ts        -> text "Glue" <+> showVal1 a <+> text (showSystem ts)
  VGlueElem a ts    -> text "glue" <+> showVal1 a <+> text (showSystem ts)
  VUnGlueElem a ts  -> text "unglue" <+> showVal1 a <+> text (showSystem ts)
  VUnGlueElemU v b es -> text "unglue U" <+> showVals [v,b]
                         <+> text (showSystem es)
  VCompU a ts       -> text "comp (<_> U)" <+> showVal1 a <+> text (showSystem ts)
  VId a u v           -> text "Id" <+> showVals [a,u,v]
  VIdPair b ts        -> text "IdC" <+> showVal1 b <+> text (showSystem ts)
  VIdJ a t c d x p    -> text "IdJ" <+> showVals [a,t,c,d,x,p]

showPLam :: Val -> Doc
showPLam e = case e of
  VPLam i a@VPLam{} -> text (show i) <+> showPLam a
  VPLam i a         -> text (show i) <> char '>' <+> showVal a
  _                 -> showVal e

-- Merge lambdas of the same type
showLam :: Val -> Doc
showLam e = case e of
  VLam x t a@(VLam _ t' _)
    | t == t'   -> text x <+> showLam a
    | otherwise ->
      text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal a
  VPi _ (VLam x t a@(VPi _ (VLam _ t' _)))
    | t == t'   -> text x <+> showLam a
    | otherwise ->
      text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal a
  VLam x t e         ->
    text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal e
  VPi _ (VLam x t e) ->
    text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal e
  _ -> showVal e

showVal1 :: Val -> Doc
showVal1 v = case v of
  VU                -> showVal v
  VCon c []         -> showVal v
  VVar{}            -> showVal v
  VFst{}            -> showVal v
  VSnd{}            -> showVal v
  Ter t@Sum{} rho   -> showTer t <+> showEnv False rho
  Ter t@HSum{} rho  -> showTer t <+> showEnv False rho
  Ter t@Split{} rho -> showTer t <+> showEnv False rho
  Ter t rho         -> showTer1 t <+> showEnv True rho
  _                 -> parens (showVal v)

showVals :: [Val] -> Doc
showVals = hsep . map showVal1

-}
