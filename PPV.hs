{-# LANGUAGE TemplateHaskell #-}
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
module PPV where

import Control.Applicative
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.RWS hiding (Sum)
import Control.Monad.Identity
import Data.List
import Data.Maybe
import Data.String (IsString(..))
import Data.Map (Map,(!),filterWithKey,elems,toList)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T

import System.Console.ANSI

import CTT
import Connections

import Text.PrettyPrint.Final
import Text.PrettyPrint.Final.Words
import qualified Text.PrettyPrint.Final.Words as W
import Text.PrettyPrint.Final.Extensions.Precedence
import Text.PrettyPrint.Final.Rendering.Console

--------------------------------------------------------------------------------
-- | syntax sugars

(>+>) :: (MonadPretty w ann fmt m) => m () -> m () -> m ()
x >+> y = x >> space 1 >> y

mpconcat :: (MonadPretty w ann fmt m) => [m ()] -> m ()
mpconcat []     = return ()
mpconcat (e:es) = e >> (mpconcat es)

str :: (MonadPretty w ann fmt m) => [Char] -> m ()
str = text . T.pack
--------------------------------------------------------------------------------
-- | setting up

data Ann = Kwd | HoleAnn | VarAnn Text | Ctor | Elim | TCtor
  deriving (Eq, Ord, Show)

toSGR :: Ann -> [SGR]
toSGR Kwd        = [SetConsoleIntensity BoldIntensity, SetUnderlining SingleUnderline]
toSGR Ctor       = [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Magenta]
toSGR Elim       = [SetConsoleIntensity BoldIntensity, SetColor Foreground Dull Magenta]
toSGR TCtor      = [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
toSGR HoleAnn    = [SetColor Background Vivid Cyan]
toSGR (VarAnn s) = case s of
  "Path"   -> [SetItalicized True, SetColor Foreground Vivid Cyan]
  "Global" -> [SetItalicized False, SetColor Foreground Vivid Green]
  _        -> [SetItalicized True, SetColor Foreground Vivid Blue]

updateColor :: StateT [Ann] IO ()
updateColor =
  lift . setSGR =<< mconcat . map toSGR . reverse <$> get

openTag :: Ann -> StateT [Ann] IO ()
openTag ann = modify (ann:) >> updateColor

closeTag :: Ann -> StateT [Ann] IO ()
closeTag _  = modify tail   >> updateColor

renderAnnotation :: Ann -> StateT [Ann] IO () -> StateT [Ann] IO ()
renderAnnotation a o = openTag a >> o >> closeTag a

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

type TEnv = Map Text Text

tEnv0 :: TEnv
tEnv0 = Map.empty

runDocM :: PEnv Int Ann () -> PrecEnv Ann -> TEnv -> PState Int () -> DocM a -> Maybe (PState Int (), POut Int Ann, a)
runDocM e pe te s d = (\(a,s',o) -> (s',o,a)) <$> runReaderT (runRWST (runPrecT pe $ unDocM d) e s) te

askTEnv :: DocM TEnv
askTEnv = DocM $ lift $ lift ask

localTEnv :: (TEnv -> TEnv) -> DocM a -> DocM a
localTEnv f = DocM . mapPrecT (mapRWST (local f)) . unDocM

--------------------------------------------------------------------------------
-- | Doc

type Doc = DocM ()

env0 :: (Num w) => PEnv w ann ()
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

class Pretty a where
  pretty :: a -> Doc

instance Pretty Doc where
  pretty = id

instance Pretty Text where
  pretty = text . T.pack . show

--------------------------------------------------------------------------------
-- | pp functions

ppFormula :: Formula -> Doc
ppFormula phi = case phi of
  _ :\/: _ -> W.parens $ str $ show phi
  _ :/\: _ -> W.parens $ str $ show phi
  _        -> str $ show phi

ppSystem :: Pretty a => System a -> Doc
ppSystem = ppListSystem . toList

ppListSystem :: Pretty a => [(Face , a)] -> Doc
ppListSystem [] = text "[]"
ppListSystem ts =
  text "[ " >>
  (mpconcat $ punctuate (text ", ")
                        [ str (showFace alpha ++ " -> ") >> pretty u
                        | (alpha,u) <- ts ]) >>
  text " ]"

  {-
ppDecls :: Decls -> Doc
ppDecls ds = case ds of
  MutualDecls _ defs -> hsep $ punctuate comma [localTEnv (Map.insert (T.pack x) "Bound") $ str x >+> equals >+> ppTer d | (x,(_,d)) <- defs]
  OpaqueDecl i       -> text "opaque" >+> str i
  TransparentDecl i  -> text "transparent" >+> str i
  TransparentAllDecl -> text "transparent_all"
-}

ppTer :: Ter -> Doc
ppTer v = case v of
  U                 -> annotate TCtor $ char 'U'
  App e0 e1         -> expr $ ppTer e0 >> newline >> ppTer1 e1
  Pi e0             -> expr $ annotate TCtor "Pi" >+> ppTer e0
  Lam x t e         -> localTEnv (Map.insert (T.pack x) "B") $ expr $ do
                         annotate Ctor (char '\\')
                         W.parens $ do
                           str x
                           space 1 >> colon >> space 1
                           ppTer t
                         space 1
                         annotate Ctor (text "->")
                         nest 2 $ do newline; ppTer e
  Fst e             -> ppTer1 e >> annotate Elim ".1"
  Snd e             -> ppTer1 e >> annotate Elim ".2"
  Sigma e0          -> expr $ annotate TCtor "Sigma" >+> ppTer1 e0
  Pair e0 e1        -> expr $ annotate Ctor (char '(') >> ppTer e0 >> annotate Ctor comma >> ppTer e1 >> annotate Ctor (char ')')
  Where e d         -> case d of
    --MutualDecls _ defs -> {-map \x (localTEnv (Map.insert (T.pack x) "Bound")) $-} ppTer e >> newline >> (annotate Kwd $ text "where") >> newline >> (hsep $ punctuate comma [str x >+> equals >+> ppTer d | (x,(_,d)) <- defs])
    MutualDecls _ defs -> localTEnv (\env -> foldr (\x -> Map.insert x "B") env [T.pack x | (x,(_,d)) <- defs]) >> expr $ do 
                               ppTer e
                               newline
                               annotate Kwd $ text "where"
                               newline
                               hsep $ punctuate comma [str x >+> equals >+> ppTer d | (x,(_,d)) <- defs]
    OpaqueDecl i       -> ppTer e >> newline >> (annotate Kwd $ text "where") >> newline >> text "opaque" >+> str i
    TransparentDecl i  -> ppTer e >> newline >> (annotate Kwd $ text "where") >> newline >> text "transparent" >+> str i
    TransparentAllDecl -> ppTer e >> newline >> (annotate Kwd $ text "where") >> newline >> text "transparent_all"
  -- Where e d         -> ppTer e >> newline >> (annotate Kwd $ text "where") >> newline >> ppDecls d
  Var x             -> do tEnv <- askTEnv
                          case Map.lookup (T.pack x) tEnv of
                            Nothing -> annotate (VarAnn "Global") (str x)
                            Just tt -> annotate (VarAnn tt) (str x)
--  Var x             -> annotate (VarAnn "B") $ text $ T.pack x
  Con c es          -> str c >+> ppTers es
  PCon c a es phis  -> expr $ do
                         str c
                         space 1
                         braces $ ppTer a
                         space 1
                         ppTers es
                         space 1
                         hsep $ map (((annotate Ctor $ char '@') >+> ) . ppFormula) phis
  Split f _ _ _     -> str f
  Sum _ n _         -> str n
  HSum _ n _        -> str n
  Undef{}           -> annotate Kwd "undefined"
  Hole{}            -> text "?"
  PathP e0 e1 e2    -> (annotate Kwd "PathP") >+> ppTers [e0,e1,e2]
  PLam i e          -> localTEnv (Map.insert (T.pack $ show i) "Path") $ expr $ do
                         annotate Ctor $ char '<'
                         str (show i)
                         annotate Ctor $ char '>'
                         space 1
                         ppTer e
  AppFormula e phi  -> ppTer1 e >+> (annotate Ctor $ char '@') >+> ppFormula phi
  Comp e t ts       -> annotate Kwd "comp" >+> ppTers [e,t] >+> ppSystem ts
  Fill e t ts       -> annotate Kwd "fill" >+> ppTers [e,t] >+> ppSystem ts
  Glue a ts         -> annotate Kwd "Glue" >+> ppTer a >+> ppSystem ts
  GlueElem a ts     -> annotate Kwd "glue" >+> ppTer a >+> ppSystem ts
  UnGlueElem a ts   -> annotate Kwd "unglue" >+> ppTer a >+> ppSystem ts
  Id a u v          -> expr $ (annotate Kwd "Id") >+> ppTers [a,u,v]
  IdPair b ts       -> annotate Kwd (text "IdC") >+> ppTer b >+> ppSystem ts
  IdJ a t c d x p   -> expr $ (annotate Kwd "IdJ") >+> ppTers [a,t,c,d,x,p]

ppTers :: [Ter] -> Doc
ppTers = vsep . map ppTer1

ppTer1 :: Ter -> Doc
ppTer1 t = case t of
  U        -> annotate TCtor $ char 'U'
  Con c [] -> text $ T.pack c
  Var{}    -> ppTer t
  Undef{}  -> ppTer t
  Hole{}   -> ppTer t
  Split{}  -> ppTer t
  Sum{}    -> ppTer t
  HSum{}   -> ppTer t
  Fst{}    -> ppTer t
  Snd{}    -> ppTer t
  _        -> W.parens $ ppTer t

instance Pretty Ter where
  pretty = ppTer

ppVal :: Val -> Doc
ppVal v = case v of
  VU                     -> annotate TCtor (char 'U')
  Ter t@Sum{} rho        -> ppTer t >+> ppEnv False rho
  Ter t@HSum{} rho       -> ppTer t >+> ppEnv False rho
  Ter t@Split{} rho      -> ppTer t >+> ppEnv False rho
  Ter t rho              -> ppTer t >+> ppEnv True rho
  VCon c us              -> str c >+> ppVals us
  VPCon c a us phis      -> str c >+> braces (ppVal a) >+> ppVals us >> hsep (map (((annotate Ctor $ char '@') >> space 1 >>) . ppFormula) phis)
  VHComp v0 v1 vs        -> annotate Kwd (text "hComp") >+> ppVals [v0,v1] >+> ppSystem vs
  VPi a l@(VLam x t b)
    | "_" `isPrefixOf` x -> ppVal1 a >+> annotate Ctor (text "->") >+> ppVal1 b
    | otherwise          -> char '(' >> ppLam (VPi a l)
  VPi a b                -> annotate TCtor (text "Pi") >+> ppVals [a,b]
  VPair u v              -> annotate Ctor (text "(") >> ppVal u >> annotate Ctor comma >> ppVal v >> annotate Ctor ")"
  VSigma u v             -> annotate TCtor (text "Sigma") >+> ppVals [u,v]
  VApp u v               -> ppVal u >+> ppVal1 v
  VLam{}                 -> text "\\(" >> ppLam v
  VPLam{}                -> annotate Ctor (char '<') >> ppPLam v
  VSplit u v             -> ppVal u >+> ppVal1 v
  VVar x _               -> str x
  VOpaque x _            -> str x
  VFst u                 -> ppVal1 u >+> annotate Elim ".1"
  VSnd u                 -> ppVal1 u >+> annotate Elim ".2"
  VPathP v0 v1 v2        -> annotate Kwd (text "PathP") >+> ppVals [v0,v1,v2]
  VAppFormula v phi      -> ppVal v >+> annotate Ctor (char '@') >> ppFormula phi
  VComp v0 v1 vs         -> annotate Kwd (text "comp") >+> ppVals [v0,v1] >+> ppSystem vs
  VGlue a ts             -> annotate Kwd (text "Glue") >+> ppVal1 a >+> ppSystem ts
  VGlueElem a ts         -> annotate Kwd (text "glue" )>+> ppVal1 a >+> ppSystem ts
  VUnGlueElem a ts       -> annotate Kwd (text "unglue") >+> ppVal1 a >+> ppSystem ts
  VUnGlueElemU v b es    -> annotate Kwd (text "unglue U") >+> ppVals [v,b] >> ppSystem es
  VCompU a ts            -> annotate Kwd (text "comp") >>  text "(" >> annotate Ctor (text "<_>") >> text "U)" >+> ppVal1 a >+> ppSystem ts
  VId a u v              -> annotate Kwd (text "Id") >+> ppVals [a,u,v]
  VIdPair b ts           -> annotate Kwd (text "IdC") >+> ppVal1 b >> ppSystem ts
  VIdJ a t c d x p       -> annotate Kwd (text "IdJ") >+> ppVals [a,t,c,d,x,p]

ppVals :: [Val] -> Doc
ppVals = hsep . map ppVal1

ppVal1 :: Val -> Doc
ppVal1 v = case v of
  VU                -> ppVal v
  VCon c []         -> ppVal v
  VVar{}            -> ppVal v
  VFst{}            -> ppVal v
  VSnd{}            -> ppVal v
  Ter t@Sum{} rho   -> ppTer t >+> ppEnv False rho
  Ter t@HSum{} rho  -> ppTer t >+> ppEnv False rho
  Ter t@Split{} rho -> ppTer t >+> ppEnv False rho
  Ter t rho         -> ppTer t >+> ppEnv True rho
  _                 -> W.parens $ ppVal v

ppEnv :: Bool -> Env -> Doc
ppEnv b e =
  let
    names x  = if b then str x >+> equals else mempty
    par x    = if b then W.parens x else x
    com      = if b then comma else mempty
    ppEnv1 e = case e of
      (Upd x env,u:us,fs,os)   ->
        ppEnv1 (env,us,fs,os) >+> names x >+> ppVal1 u >> com
      (Sub i env,us,phi:fs,os) ->
        ppEnv1 (env,us,fs,os) >+> names (show i) >+> str (show phi) >> com
      (Def _ _ env,vs,fs,os)   -> ppEnv1 (env,vs,fs,os)
      _                        -> ppEnv b e
  in case e of
    (Empty,_,_,_)            -> mempty
    (Def _ _ env,vs,fs,os)   -> ppEnv b (env,vs,fs,os)
    (Upd x env,u:us,fs,os)   ->
      par $ ppEnv1 (env,us,fs,os) >+> names x >+> ppVal1 u
    (Sub i env,us,phi:fs,os) ->
      par $ ppEnv1 (env,us,fs,os) >+> names (show i) >+> str (show phi)

ppLam :: Val -> Doc
ppLam e = case e of
  VLam x t a@(VLam _ t' _)
    | t == t'        -> localTEnv (Map.insert (T.pack x) "B") $ str x >+> ppLam a
    | otherwise      -> localTEnv (Map.insert (T.pack x) "B") $ str x >+> colon >+> ppVal t >> char ')' >+> annotate Ctor (text "->") >+> ppVal a
  VPi _ (VLam x t a@(VPi _ (VLam _ t' _)))
    | t == t'        -> localTEnv (Map.insert (T.pack x) "B") $ str x >+> ppLam a
    | otherwise      -> localTEnv (Map.insert (T.pack x) "B") $ str x >+> colon >+> ppVal t >> char ')' >+> annotate Ctor (text "->") >+> ppVal a
  VLam x t e         ->
    localTEnv (Map.insert (T.pack x) "B") $ str x >+> colon >+> ppVal t >> char ')' >+> annotate Ctor (text "->") >+> ppVal e
  VPi _ (VLam x t e) ->
    localTEnv (Map.insert (T.pack x) "B") $ str x >> colon >+> ppVal t >> char ')' >+> annotate Ctor (text "->") >+> ppVal e
  _                  -> ppVal e

ppPLam :: Val -> Doc
ppPLam e = case e of
  VPLam i a@VPLam{} -> localTEnv (Map.insert (T.pack (show i)) "B") $ str (show i) >+> ppPLam a
  VPLam i a         -> localTEnv (Map.insert (T.pack (show i)) "B") $ str (show i) >> annotate Ctor (char '>') >+> ppVal a
  _                 -> ppVal e

instance Pretty Val where
  pretty = ppVal

dumpVal :: Val -> IO ()
dumpVal = dumpDoc toSGR renderAnnotation . execDoc . pretty
