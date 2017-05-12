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

data Ann = Kwd | HoleAnn | VarAnn Text | Ctor | Elim | TCtor
  deriving (Eq, Ord, Show)

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

newtype DocM a = DocM { unDocM :: PrecT Ann (RWST (PEnv Int Ann ()) (POut Int Ann) (PState Int ()) (ReaderT TEnv Maybe)) a }
  deriving
    ( Functor, Applicative, Monad, Alternative
    , MonadReader (PEnv Int Ann ()), MonadWriter (POut Int Ann), MonadState (PState Int ())
    , MonadReaderPrec Ann
    )
instance MonadPretty Int Ann () DocM
instance MonadPrettyPrec Int Ann () DocM

{-
newtype DocM a = DocM { unDocM :: RWST (PEnv Int Ann ()) (POut Int Ann) (PState Int ()) Maybe a }
  deriving
    ( Functor, Applicative, Monad
    , MonadReader (PEnv Int Ann ()), MonadWriter (POut Int Ann), MonadState (PState Int ()), Alternative
    )

instance MonadPretty Int Ann () DocM
-}

instance Measure Int () DocM where
  measure = return . runIdentity . measure

type TEnv = Map Text Text

tEnv0 :: TEnv
tEnv0 = Map.empty


runDocM :: PEnv Int Ann () -> PrecEnv Ann -> TEnv -> PState Int () -> DocM a -> Maybe (PState Int (), POut Int Ann, a)
runDocM e pe te s d = (\(a,s',o) -> (s',o,a)) <$> runReaderT (runRWST (runPrecT pe $ unDocM d) e s) te

  {-
runDocM :: PEnv Int Ann () -> PState Int () -> DocM a -> Maybe (PState Int (), POut Int Ann, a)
runDocM e s d = (\(a,s',o) -> (s',o,a)) <$> runRWST (unDocM d) e s
-}

askTEnv :: DocM TEnv
askTEnv = DocM $ lift $ lift ask

localTEnv :: (TEnv -> TEnv) -> DocM a -> DocM a
localTEnv f = DocM . mapPrecT (mapRWST (local f)) . unDocM

-- Doc
type Doc = DocM ()

execDoc :: Doc -> POut Int Ann
execDoc d =
  let rM = runDocM env0 precEnv0 tEnv0 state0 d
  in case rM of
    Nothing -> PAtom $ AChunk $ CText "<internal pretty printing error>"
    Just (_, o, ()) -> o

  {-
execDoc :: Doc -> POut Int Ann
execDoc d =
  let rM = runDocM env0 state0 d
  in case rM of
    Nothing -> PAtom $ AChunk $ CText "<internal pretty printing error>"
    Just (_, o, ()) -> o
-}

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

ppFormula :: Formula -> Doc
ppFormula phi = case phi of
  _ :\/: _ -> W.parens (text $ T.pack (show phi))
  _ :/\: _ -> W.parens (text $ T.pack (show phi))
  _ -> text $ T.pack $ show phi

ppSystem :: Pretty a => System a -> Doc
ppSystem = ppListSystem . toList

mpconcat :: (MonadPretty w ann fmt m) => [m ()] -> m ()
mpconcat []     = return ()
mpconcat (e:es) = e >> (mpconcat es)

ppListSystem :: Pretty a => [(Face , a)] -> Doc
ppListSystem [] = text "[]"
ppListSystem ts =
  text "[ " >>
  (mpconcat (punctuate (text ", ") [ (text (T.pack (showFace alpha ++ " -> "))) >> (pretty u)
                         | (alpha,u) <- ts ])) >>
  text " ]"

ppDecls :: Decls -> Doc
ppDecls ds = case ds of
  MutualDecls _ defs -> hsep $ punctuate comma [(text $ T.pack x) >> space 1 >> equals >> space 1 >> ppTer d | (x,(_,d)) <- defs]
  OpaqueDecl i -> text "opaque" >> space 1 >> (text $ T.pack i)
  TransparentDecl i -> text "transparent" >> space 1 >> (text $ T.pack i)
  TransparentAllDecl -> text "transparent_all"

ppTer :: Ter -> Doc
ppTer v = case v of
  U                 -> annotate TCtor $ char 'U'
  App e0 e1         -> grouped $ ppTer e0 >> newline >> ppTer1 e1
  Pi e0             -> grouped $ (annotate TCtor $ text "Pi") >> space 1 >> ppTer e0
  Lam x t e         -> localTEnv (Map.insert (T.pack x) "Bound") $ grouped $ do
                         annotate Ctor (char '\\')
                         W.parens $ do
                           (text $ T.pack x)
                           space 1 >> colon >> space 1
                           ppTer t
                         space 1
                         (annotate Ctor $ text "->")
                         nest 2 $ do newline; ppTer e
  Fst e             -> ppTer1 e >> (annotate Elim $ text ".1")
  Snd e             -> ppTer1 e >> (annotate Elim $ text ".2")
  Sigma e0          -> grouped $ (annotate TCtor $ (text "Sigma")) >> space 1 >> ppTer1 e0
  Pair e0 e1        -> grouped $ (annotate Ctor $ text "(") >> ppTer e0 >> annotate Ctor comma >> ppTer e1 >> (annotate Ctor $ text ")")
  Where e d         -> ppTer e >> newline >> (annotate Kwd $ text "where") >> newline >> ppDecls d
  {-
  Var x             -> do tEnv <- askTEnv
                          let tt = tEnv Map.! T.pack x
                          annotate (VarAnn tt) $ text $ T.pack x
-}
  Var x             -> annotate (VarAnn "Normal") $ text $ T.pack x
  Con c es          -> (text $ T.pack c) >> space 1 >> ppTers es
  PCon c a es phis  -> grouped $ do
                         text $ T.pack c
                         space 1
                         braces $ ppTer a
                         space 1
                         ppTers es
                         space 1
                         hsep $ map (((annotate Ctor $ char '@') >> space 1 >> ) . ppFormula) phis
  Split f _ _ _     -> text $ T.pack f
  Sum _ n _         -> text $ T.pack n
  HSum _ n _        -> text $ T.pack n
  Undef{}           -> (annotate Kwd $ text "undefined")
  Hole{}            -> text "?"
  PathP e0 e1 e2    -> (annotate Kwd $ text "PathP") >> space 1 >> ppTers [e0,e1,e2]
  PLam i e          -> localTEnv (Map.insert (T.pack $ show i) "Path") $ (annotate Ctor $ char '<') >> (text $ T.pack (show i)) >> (annotate Ctor $ char '>') >> space 1 >> ppTer e
  AppFormula e phi  -> ppTer1 e >> space 1 >> (annotate Ctor $ char '@') >> space 1 >> ppFormula phi
  Comp e t ts       -> (annotate Kwd $ text "comp") >> space 1 >> ppTers [e,t] >> space 1 >> ppSystem ts
  Fill e t ts       -> (annotate Kwd $ text "fill") >> space 1 >> ppTers [e,t] >> space 1 >> ppSystem ts
  Glue a ts         -> (annotate Kwd $ text "Glue") >> space 1 >> ppTer a >> space 1 >> ppSystem ts
  GlueElem a ts     -> (annotate Kwd $ text "glue") >> space 1 >> ppTer a >> space 1 >> ppSystem ts
  UnGlueElem a ts   -> (annotate Kwd $ text "unglue") >> space 1 >> ppTer a >> space 1 >> ppSystem ts
  Id a u v          -> grouped $ (annotate Kwd $ text "Id") >> space 1 >> ppTers [a,u,v]
  IdPair b ts       -> (annotate Kwd $ text "IdC") >> space 1 >> ppTer b >> space 1 >> ppSystem ts
  IdJ a t c d x p   -> grouped $ (annotate Kwd $ text "IdJ") >> space 1 >> ppTers [a,t,c,d,x,p] 

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
  _        -> W.parens (ppTer t)

instance Pretty Ter where
  pretty = ppTer

ppVal :: Val -> Doc
ppVal v = case v of
  VU                     -> annotate TCtor $ char 'U'
  Ter t@Sum{} rho        -> ppTer t >> space 1 >> ppEnv False rho 
  Ter t@HSum{} rho       -> ppTer t >> space 1 >> ppEnv False rho
  Ter t@Split{} rho      -> ppTer t >> space 1 >> ppEnv False rho
  Ter t rho              -> ppTer t >> space 1 >> ppEnv True rho 
  VCon c us              -> (text $ T.pack c) >> space 1 >> ppVals us
  VPCon c a us phis      -> (text $ T.pack c) >> space 1 >> braces (ppVal a) >> space 1 >> ppVals us >> hsep (map (((annotate Ctor $ char '@') >> space 1 >>) . ppFormula) phis)
  VHComp v0 v1 vs        -> (annotate Kwd $ text "hComp") >> space 1 >> ppVals [v0,v1] >> space 1 >> ppSystem vs
  VPi a l@(VLam x t b)
    | "_" `isPrefixOf` x -> ppVal1 a >> space 1 >> (annotate Ctor $ text "->") >> space 1 >> ppVal1 b
    | otherwise          -> char '(' >> ppLam (VPi a l)
  VPi a b                -> (annotate TCtor $ text "Pi") >> space 1 >> ppVals [a,b] 
  VPair u v              -> (annotate Ctor $ text "(") >> ppVal u >> (annotate Ctor comma) >> ppVal v >> (annotate Ctor ")")
  VSigma u v             -> (annotate TCtor $ text "Sigma") >> space 1 >> ppVals [u,v]
  VApp u v               -> ppVal u >> space 1 >> ppVal1 v
  VLam{}                 -> text "\\(" >> ppLam v
  VPLam{}                -> (annotate Ctor $ char '<') >> ppPLam v
  VSplit u v             -> ppVal u >> space 1 >> ppVal1 v
  VVar x _               -> text $ T.pack x
  VOpaque x _            -> text $ T.pack x
  VFst u                 -> ppVal1 u >> space 1 >> (annotate Elim ".1")
  VSnd u                 -> ppVal1 u >> space 2 >> (annotate Elim ".2")
  VPathP v0 v1 v2        -> (annotate Kwd $ text "PathP") >> space 1 >> ppVals [v0,v1,v2]
  VAppFormula v phi      -> ppVal v >> space 1 >> (annotate Ctor $ char '@') >> ppFormula phi
  VComp v0 v1 vs         -> (annotate Kwd $ text "comp") >> space 1 >> ppVals [v0,v1] >> space 1 >> ppSystem vs
  VGlue a ts             -> (annotate Kwd $ text "Glue") >> space 1 >> ppVal1 a >> space 1 >> ppSystem ts
  VGlueElem a ts         -> (annotate Kwd $ text "glue") >> space 1 >> ppVal1 a >> space 1 >> ppSystem ts
  VUnGlueElem a ts       -> (annotate Kwd $ text "unglue") >> space 1 >> ppVal1 a >> space 1 >> ppSystem ts
  VUnGlueElemU v b es    -> (annotate Kwd $ text "unglue U") >> space 1 >> ppVals [v,b] >> ppSystem es
  VCompU a ts            -> (annotate Kwd $ text "comp") >>  text "(" >> (annotate Ctor $ text "<_>") >> text "U)" >> space 1 >> ppVal1 a >> space 1 >> ppSystem ts
  VId a u v              -> (annotate Kwd $ text "Id") >> space 1 >> ppVals [a,u,v]
  VIdPair b ts           -> (annotate Kwd $ text "IdC") >> space 1 >> ppVal1 b >> ppSystem ts
  VIdJ a t c d x p       -> (annotate Kwd $ text "IdJ") >> space 1 >> ppVals [a,t,c,d,x,p]

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
  _                 -> W.parens (ppVal v)

ppEnv :: Bool -> Env -> Doc
ppEnv b e =
  let
    names x  = if b then text x >> space 1 >> equals else mempty
    par x    = if b then W.parens x else x
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

ppLam :: Val -> Doc
ppLam e = case e of
  VLam x t a@(VLam _ t' _)
    | t == t'   -> localTEnv (Map.insert (T.pack x) "Normal") $ (text $ T.pack x) >> space 1 >> ppLam a
    | otherwise -> localTEnv (Map.insert (T.pack x) "Normal") $ (text $ T.pack x) >> space 1 >> colon >> space 1 >> ppVal t >> char ')' >> space 1 >> (annotate Ctor $ text "->") >> space 1 >> ppVal a
  VPi _ (VLam x t a@(VPi _ (VLam _ t' _)))
    | t == t'   -> localTEnv (Map.insert (T.pack x) "Normal") $ (text $ T.pack x) >> space 1 >> ppLam a
    | otherwise -> localTEnv (Map.insert (T.pack x) "Normal") $ (text $ T.pack x) >> space 1 >> colon >> space 1 >> ppVal t >> char ')' >> space 1 >> (annotate Ctor $ text "->") >> space 1 >> ppVal a
  VLam x t e ->
    localTEnv (Map.insert (T.pack x) "Normal") $ (text $ T.pack x) >> space 1 >> colon >> space 1 >> ppVal t >> char ')' >> space 1 >> (annotate Ctor $ text "->") >> space 1 >> ppVal e
  VPi _ (VLam x t e) ->
    localTEnv (Map.insert (T.pack x) "Normal") $ (text $ T.pack x) >> colon >> space 1 >> ppVal t >> char ')' >> space 1 >>  (annotate Ctor $ text "->") >> space 1 >> ppVal e
  _ -> ppVal e

ppPLam :: Val -> Doc
ppPLam e = case e of
  VPLam i a@VPLam{} -> localTEnv (Map.insert (T.pack (show i)) "Normal") $ (text $ T.pack (show i)) >> space 1 >> ppPLam a
  VPLam i a -> localTEnv (Map.insert (T.pack (show i)) "Normal") $ (text $ T.pack (show i)) >> (annotate Ctor $ char '>') >> space 1 >> ppVal a
  _ -> ppVal e

instance Pretty Val where
  pretty = ppVal

toSGR :: Ann -> [SGR]
toSGR Kwd     = [SetConsoleIntensity BoldIntensity, SetUnderlining SingleUnderline] 
toSGR Ctor    = [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Magenta]
toSGR Elim    = [SetConsoleIntensity BoldIntensity, SetColor Foreground Dull Magenta]
toSGR TCtor   = [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
toSGR HoleAnn = [SetColor Background Vivid Cyan]
toSGR (VarAnn s) = case s of
  "Path" -> [SetItalicized True, SetColor Foreground Vivid Cyan]
  _      -> [SetItalicized True, SetColor Foreground Vivid Blue] 
  
updateColor :: forall ann . StateT [Ann] IO ()
updateColor =
  lift . setSGR =<< mconcat . map toSGR . reverse <$> get

openTag :: Ann -> StateT [Ann] IO ()
openTag ann = modify (ann:) >> updateColor

closeTag :: Ann -> StateT [Ann] IO ()
closeTag _  = modify tail   >> updateColor

renderAnnotation :: Ann -> StateT [Ann] IO () -> StateT [Ann] IO ()
renderAnnotation a o = openTag a >> o >> closeTag a

dumpVal :: Val -> IO ()
dumpVal = dumpDoc toSGR renderAnnotation . execDoc . pretty 
