

-- UUAGC 0.9.52.1 (Ruler.ag)
module Main where

import System.Environment
import System.IO
import System.Console.GetOpt
import Data.Maybe
import Data.Char
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import UHC.Util.FPath
import UHC.Util.Utils
import UHC.Util.Pretty
import UHC.Util.PrettyUtils
import UU.Parsing
import UU.Scanner
import UU.Scanner.Position( initPos, Pos )

-------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------

main :: IO ()
main
  = do { args <- getArgs
       ; let oo@(o,n,errs)  = getOpt Permute cmdLineOpts args
             opts           = foldr ($) defaultOpts o
       ; if optHelp opts
         then putStrLn (usageInfo "Usage ruler [options] [file]\n\noptions:" cmdLineOpts)
         else if null errs
              then  doCompile (if null n then emptyFPath else mkFPath (head n)) opts
              else  putStr (head errs)
       }

doCompile :: FPath -> Opts -> IO ()
doCompile fp opts
  = do { (fn,fb,fh)
             <- if fpathIsEmpty fp
                then return ("<stdin>","<stdin>",stdin)
                else do { let fn = fpathToStr fp
                        ; h <- openFile fn ReadMode
                        ; return (fn,fpathToStr (fpathRemoveSuff fp),h)
                        }
       ; tokens <- scanHandle keywordsText keywordsOps specialChars opChars fn fh
       ; pres <- parseIO (pAGItf) tokens
       ; let res = wrap_AGItf pres
                     (Inh_AGItf
                        { opts_Inh_AGItf = opts
                        })
       ; putBld (optLaTeX opts) (ppLaTeX_Syn_AGItf res) 
       ; return ()
       }
  where putBld f b
          = if f
            then putStrLn (disp b 2000 "")
            else return ()

-------------------------------------------------------------------------
-- Options
-------------------------------------------------------------------------

data Opts 
  = Opts
      { optLaTeX        :: Bool
      , optHelp         :: Bool
      , optWrapLhs2tex  :: Bool
      , optBaseNm       :: String
      }

defaultOpts
  = Opts
      { optLaTeX        =  False
      , optHelp         =  False
      , optWrapLhs2tex  =  True
      , optBaseNm       =  rulesCmdPre
      }

cmdLineOpts  
  =  [ Option "l"  ["latex"]     (NoArg oLaTeX)
          "generate code for latex, default=no"
     , Option ""   ["help"]      (NoArg oHelp)
          "output this help"
     , Option "b"  ["base"]      (ReqArg oBase "<name>")
          "base name, default = 'rules'"
     , Option ""   ["lhs2tex"]   (OptArg oLhs2tex "yes|no")
          "wrap chunks in lhs2tex's code environment, default=yes (not implemented)"
     ]
  where  oLaTeX          o =  o {optLaTeX = True}
         oLhs2tex    ms  o =  yesno (\f o -> o {optWrapLhs2tex = f}) ms o
         oHelp           o =  o {optHelp = True}
         oBase       s   o =  o {optBaseNm = s}
         yesno updO  ms  o =  case ms of
                                Just "yes"  -> updO True o
                                Just "no"   -> updO False o
                                _           -> o


-------------------------------------------------------------------------
-- Scanning
-------------------------------------------------------------------------

specialChars  =  "().`"
opChars       =  "!#$%&*+/<=>?@\\^|-:;,[]{}~"

keywordsTextEscapable
  =  [ "judge", "rule", "rules", "cond", "preamble", "scheme", "view", "viewset", "let", "in" ]
keywordsText
  =  [ "viewas" ] ++ keywordsTextEscapable
keywordsOps   =  [ "=", "-", "&", "\\\\" ]

scanHandle :: [String] -> [String] -> String -> String -> FilePath -> Handle -> IO [Token]
scanHandle keywordstxt keywordsops specchars opchars fn fh
  = do  {  txt <- hGetContents fh
        ;  return (scan keywordstxt keywordsops specchars opchars (initPos fn) txt) 
        }

-------------------------------------------------------------------------
-- Parser
-------------------------------------------------------------------------

type MkConAppAlg t = (String -> t,t -> t -> t,t -> t)

mkApp :: MkConAppAlg t -> [t] -> t
mkApp (_,app,top) ts
  = case ts of
      [t]  -> t
      _    -> top t
  where t = foldl1 app ts

pAGItf :: (IsParser p Token) => p T_AGItf
pAGItf
  = let alg                 =   (undefined,sem_JExpr_App,sem_JExpr_AppTop)
        pAGItf              =   sem_AGItf_AGItf <$ pKey "preamble" <*> pString <*> pDecls
        pDecls              =   pFoldr (sem_Decls_Cons,sem_Decls_Nil) pDecl
        pDecl               =   sem_Decl_Scheme <$  pKey "scheme" <*> pNm <* pKey "="
                                                <*> pJExpr <* pKey "="
                                                <*> pJExpr
                                                <*> pViews
                            <|> sem_Decl_Rules <$  pKey "rules" <*> pNmSuff
                                               <*> pString <*> pOptViewSels
                                               <*  pKey "=" <*> pViews <*> pRules
                            <|> sem_Decl_ViewSet <$  pKey "viewset" <*> pNm
                                                 <*  pKey "=" <*> pViewSels
                            <|> sem_Decl_View <$> pView
        pViews              =   pFoldr (sem_Views_Cons,sem_Views_Nil) pView
        pView               =   sem_View_View <$ pKey "view" <*> pViewSels <* pKey "=" <*> pJExprLet
        pViewSel            =   sem_ViewSel_One <$> pNm'
        pViewSels           =   pFoldr (sem_ViewSels_Cons,sem_ViewSels_Nil) pViewSel
        pViewAsSels         =   pKey "viewas" *> pViewSels
        pOptViewSels        =   pViewAsSels `opt` sem_ViewSels_Nil
        pRules              =   pFoldr (sem_Rules_Cons,sem_Rules_Nil) pRule
        pRule               =   ((,,) <$> (True <$ pKey "&" <|> pSucceed False) <*  pKey "rule" <*> pNm <*> pOptViewSels <* pKey "=")
                                <**> (   (\pre post (hor,nm,vsel) -> sem_Rule_Rule hor nm vsel pre post) <$> pRExprViews <* pKey "-" <*> pRExprViews
                                     <|> (\alias (hor,nm,vsel) -> sem_Rule_RuleUse hor nm vsel alias) <$ pKey "rule" <*> pNmSuff
                                     )
        pNm                 =   pVarid <|> pConid
        pNm'                =   pNm <|> pInteger
        pNmSuff             =   (:) <$> pNm <*> pList (pKey "." *> pNm')
        pSym                =   pVarsym <|> pConsym <|> (\q n -> q ++ n ++ q) <$> pKey "`" <*> pNm <* pKey "`"
        pRExpr              =   sem_RExpr_Judge <$> pJudge
                            <|> sem_RExpr_Cond <$ pKey "cond" <*> pJExpr
        pRExprViews         =   pFoldr (sem_RExprViews_Cons,sem_RExprViews_Nil) pRExprView
        pRExprView          =   sem_RExprView_RExpr <$> pRExpr <*> pOptViewSels
        pJudge              =   sem_Judge_Judge <$ pKey "judge" <*> pNm <*> pJExpr
        pJExprLet           =   (\d b -> foldr (\(n,v) b -> sem_JExpr_Let n v b) b d) <$ pKey "let" <*> pListSep (pKey "&") ((,) <$> pNm <* pKey "=" <*> pJExpr) <* pKey "in" <*> pJExpr
                            <|> pJExpr
        pJExpr              =   pChainr pOp pJExprApp
                            where pOp = (\s ss -> sem_JExpr_Op s (ss (sem_JExpr_Var s))) <$> pSym <*> pJExprSel
        pJExprApp           =   mkApp alg <$> pList1 (pJExprBase <**> pJExprSel) <|> pSucceed sem_JExpr_Empty
        pJExprBase          =   sem_JExpr_Paren <$> pParens pJExpr
                            <|> sem_JExpr_Var <$> pNm'
                            <|> sem_JExpr_Str <$> pString
                            <|> pParens (pJExprEsc <|> pJExprViewAs)
        pJExprViewAs        =   mkApp alg <$> pList1 (sem_JExpr_ViewAs <$> pViewAsSels <* pKey "=" <*> pJExpr)
        pJExprEsc           =   (sem_JExpr_StrAsIs . concat) <$> pList1 (foldr1 (<|>) . map pKey $ (["."] ++ keywordsOps ++ keywordsTextEscapable))
        pJExprMbBase        =   sem_MbJExpr_Just <$> pJExprBase <|> pSucceed sem_MbJExpr_Nothing
        pJExprSel           =   pJExprSel1 <|> pSucceed id
        pJExprSel1          =   (\ss s -> \e -> sem_JExpr_SelTop (sem_JExpr_Sel (ss e) (sem_MbJExpr_Just s))) <$> pDots <*> pJExprBase
                            where pSel' = flip sem_JExpr_Sel <$> pJExprMbBase
                                  pDots = pChainr_ng ((\s -> \_ r -> \e -> r (s e)) <$> pSel') (id <$ pKey ".")
     in pAGItf


ruleEval :: Rule -> String -> Opts -> JGlobViewGam -> JViewSetGam -> JScmGam -> JFmtGam -> JVarGam -> (PP_Doc,Bool)
ruleEval r vw o gvwg vwsg sg fg vg
  = let r1 = sem_AGRuleItf (AGRuleItf_AGItf r)
        r2 = wrap_AGRuleItf r1 (Inh_AGRuleItf {opts_Inh_AGRuleItf = o,view_Inh_AGRuleItf = vw,jGlobViewGam_Inh_AGRuleItf = gvwg,jViewSetGam_Inh_AGRuleItf = vwsg,jFmtGam_Inh_AGRuleItf = fg,jScmGam_Inh_AGRuleItf = sg,jVarGam_Inh_AGRuleItf = vg})
    in  (ppLaTeX_Syn_AGRuleItf r2,viewIsSel_Syn_AGRuleItf r2)


data JTy
  = JTy_Op      String JTy JTy JTy
  | JTy_Paren   JTy
  | JTy_Var     String
  | JTy_PP      PP_Doc
  | JTy_Any
  deriving Show

ppJTy :: JTy -> PP_Doc
ppJTy t
  = case t of
      JTy_Op _ p l r    -> ppJTy l >#< ppJTy p >#< ppJTy r
      JTy_Paren t'      -> ppParens (ppJTy t')
      JTy_Var n         -> text (mkLhs2TeXSafe n)
      JTy_PP p          -> p
      JTy_Any           -> text "*"

jtyUnPPify :: JTy -> JTy
jtyUnPPify t
  = case t of
      JTy_Op nm p l r   -> JTy_Op nm (jtyUnPPify p) (jtyUnPPify l) (jtyUnPPify r)
      JTy_Paren t'      -> JTy_Paren (jtyUnPPify t')
      JTy_PP p          -> JTy_Any
      _                 -> t

type Binds = Map.Map String JTy
data FIOut = FIOut {foTy :: JTy, foErrL :: PP_DocL, foCoe :: JTy -> JTy, foBinds :: Binds}

emptyFIOut = FIOut {foTy = JTy_Any, foErrL = [], foCoe = id, foBinds = Map.empty}

foHasErrs :: FIOut -> Bool
foHasErrs = not . null . foErrL

jtyFitsIn :: JTy -> JTy -> FIOut
jtyFitsIn ty1 ty2
  = let res t = emptyFIOut {foTy = t}
        err p = emptyFIOut {foErrL = [p]}
        coe fo c = fo {foCoe = c}
        bnd fo n t = fo {foBinds = Map.insert n t (foBinds fo)}
        bnds fo fo1 fo2 = fo {foBinds = foBinds fo2 `Map.union` foBinds fo1 `Map.union` foBinds fo}
        f t1 JTy_Any
            = res t1
        f (JTy_Paren t1) (JTy_Paren t2)
            = f t1 t2
        f t1 (JTy_Paren t2)
            = f t1 t2
        f t1 (JTy_Var v2)
            = bnd (res t1) v2 t1
        f (JTy_Op n1 p1 l1 r1) (JTy_Op n2 _ l2 r2)
            | n1 == n2
            = foldr1 (\fo1 fo2 -> if foHasErrs fo1 then fo1 else fo2) [lfo,rfo,bnds (coe (res rt) c) lfo rfo]
            where lfo = f l1 l2
                  rfo = f r1 r2
                  rt  = JTy_Op n1 p1 (foTy lfo) (foTy rfo)
                  c   = \(JTy_Op n p l r) -> JTy_Op n p (foCoe lfo l) (foCoe rfo r)
        f t1 t2
            = err ("RULER error, fitsin:" >#< ppJTy ty1 >#< "<=" >#< ppJTy ty2 >|< ", detail:" >#< ppJTy t1 >#< "<=" >#< ppJTy t2)
     in f ty1 ty2

jtyAppBinds :: Binds -> JTy -> JTy
jtyAppBinds b jt
  = let app t = case t of
                  JTy_Op nm p l r   -> JTy_Op nm (app p) (app l) (app r)
                  JTy_Paren t'      -> JTy_Paren (app t')
                  JTy_Var nm        -> maybe t id (Map.lookup nm b)
                  _                 -> t
     in app jt


data JViewSetGamInfo = JViewSetGamInfo {vwsgiViewNmS :: Set.Set String}
type JViewSetGam = Map.Map String JViewSetGamInfo


data JGlobViewGamInfo = JGlobViewGamInfo {gvwgiVarGam :: JVarGam }
type JGlobViewGam = Map.Map String JGlobViewGamInfo


data JScmGamInfo = JScmGamInfo {sgiAllViewNmL :: [String], sgiViewNmL :: [String] }
type JScmGam = Map.Map String JScmGamInfo


data JFmtGamInfo = JFmtGamInfo {fgiTy :: JTy, fgiFullTy :: JTy, fgiReplTy :: JTy, fgiVarGam :: JVarGam }
type JFmtGam = Map.Map String JFmtGamInfo

fmtAscL2JFmtGam :: String -> [(String,JFmtGamInfo)] -> JFmtGam
fmtAscL2JFmtGam prefix = Map.fromList . map (\(n,f) -> (prefix ++ n,f))


mkScmFmt :: String -> (JFmtGamInfo -> JTy) -> JFmtGam -> (JTy,[PP_Doc])
mkScmFmt n t g
  = case Map.lookup n g of
      Nothing  -> (JTy_Any,["RULER error, undefined:" >#< n])
      Just fgi -> let fo = jtyFitsIn (t fgi) (fgiTy fgi)
                   in (foBinds fo `jtyAppBinds` fgiReplTy fgi,foErrL fo)


data JVarGamInfo = JVarGamInfo {vgiPP :: PP_Doc, vgiIsEmpty :: Bool}
type JVarGam = Map.Map String JVarGamInfo


rulesCmdPre = "rules"

mkLaTeXNm :: String -> String
mkLaTeXNm = map (\c -> if isAlphaNum c then c else '-')

mkLhs2TeXSafe :: String -> String
mkLhs2TeXSafe = concat . map (\c -> if c == '|' then "||" else [c])

mkMBox :: PP a => a -> PP_Doc
mkMBox p = "\\;\\mbox" >|< ppCurly p

mkRuleNm :: String -> String -> PP_Doc
mkRuleNm r v = "\\textsc" >|< ppCurly (mkLaTeXNm r) >|< (if null v then empty else "_" >|< ppCurly v)
-- mkRuleNm r v = mkMBox (mkLaTeXNm r ++ if null v then "" else ("$_{" ++ v ++ "}$"))

mkVerb :: PP_Doc -> PP_Doc
mkVerb p = ppPacked "@" "@" p

switchLaTeXLhs :: PP a => a -> PP_Doc
switchLaTeXLhs p = ppVBar (" " >|< p >|< " ")

mkInLhs2Tex :: PP_Doc -> PP_Doc
mkInLhs2Tex p = ppVBar (p >|< " ")

ensureTeXMath :: PP_Doc -> PP_Doc
ensureTeXMath = mkTexCmdUse "ensuremath"

ppArg :: PP p => p -> PP_Doc
ppArg p = ppCurly p >|< "%"

mkCmdNmDef :: PP_Doc -> PP_Doc -> PP_Doc
mkCmdNmDef = mkTexCmdDef "rulerCmdDef"

mkCmdNmUse :: PP_Doc -> PP_Doc
mkCmdNmUse = mkTexCmdUse "rulerCmdUse"



viewIsInSel :: JViewSetGam -> String -> String -> Bool
viewIsInSel g vw selVw = selVw `Set.member` viewExpandNm g [vw]

viewExpandNm :: JViewSetGam -> [String] -> Set.Set String
viewExpandNm g
  = Set.unions . map e
  where e v = maybe (Set.singleton v) (Set.unions . map e . Set.toList . vwsgiViewNmS) (Map.lookup v g)
  
viewExpandNmL :: JViewSetGam -> [String] -> [String]
viewExpandNmL g = Set.toList . viewExpandNm g
-- AGItf -------------------------------------------------------
data AGItf = AGItf_AGItf (String) (Decls)
-- cata
sem_AGItf :: AGItf ->
             T_AGItf
sem_AGItf (AGItf_AGItf _preamble _decls) =
    (sem_AGItf_AGItf _preamble (sem_Decls _decls))
-- semantic domain
type T_AGItf = Opts ->
               ( PP_Doc)
data Inh_AGItf = Inh_AGItf {opts_Inh_AGItf :: Opts}
data Syn_AGItf = Syn_AGItf {ppLaTeX_Syn_AGItf :: PP_Doc}
wrap_AGItf :: T_AGItf ->
              Inh_AGItf ->
              Syn_AGItf
wrap_AGItf sem (Inh_AGItf _lhsIopts) =
    (let ( _lhsOppLaTeX) = sem _lhsIopts
     in  (Syn_AGItf _lhsOppLaTeX))
sem_AGItf_AGItf :: String ->
                   T_Decls ->
                   T_AGItf
sem_AGItf_AGItf preamble_ decls_ =
    (\ _lhsIopts ->
         (let _declsOgathJViewSetGam :: JViewSetGam
              _declsOjViewSetGam :: JViewSetGam
              _declsOgathJGlobViewGam :: JGlobViewGam
              _declsOjGlobViewGam :: JGlobViewGam
              _declsOgathJScmGam :: JScmGam
              _declsOjScmGam :: JScmGam
              _declsOgathJFmtGam :: JFmtGam
              _declsOjFmtGam :: JFmtGam
              _declsOjVarGam :: JVarGam
              _lhsOppLaTeX :: PP_Doc
              _declsOopts :: Opts
              _declsIgathJFmtGam :: JFmtGam
              _declsIgathJGlobViewGam :: JGlobViewGam
              _declsIgathJScmGam :: JScmGam
              _declsIgathJViewSetGam :: JViewSetGam
              _declsIppLaTeX :: PP_Doc
              _declsOgathJViewSetGam =
                  Map.empty
              _declsOjViewSetGam =
                  _declsIgathJViewSetGam
              _declsOgathJGlobViewGam =
                  Map.empty
              _declsOjGlobViewGam =
                  _declsIgathJGlobViewGam
              _declsOgathJScmGam =
                  Map.empty
              _declsOjScmGam =
                  _declsIgathJScmGam
              _declsOgathJFmtGam =
                  Map.empty
              _declsOjFmtGam =
                  _declsIgathJFmtGam
              _declsOjVarGam =
                  Map.empty
              _lhsOppLaTeX =
                  (vlist . map text . lines $ preamble_) >-< _declsIppLaTeX
              _declsOopts =
                  _lhsIopts
              ( _declsIgathJFmtGam,_declsIgathJGlobViewGam,_declsIgathJScmGam,_declsIgathJViewSetGam,_declsIppLaTeX) =
                  decls_ _declsOgathJFmtGam _declsOgathJGlobViewGam _declsOgathJScmGam _declsOgathJViewSetGam _declsOjFmtGam _declsOjGlobViewGam _declsOjScmGam _declsOjVarGam _declsOjViewSetGam _declsOopts
          in  ( _lhsOppLaTeX)))
-- AGRuleItf ---------------------------------------------------
data AGRuleItf = AGRuleItf_AGItf (Rule)
-- cata
sem_AGRuleItf :: AGRuleItf ->
                 T_AGRuleItf
sem_AGRuleItf (AGRuleItf_AGItf _rule) =
    (sem_AGRuleItf_AGItf (sem_Rule _rule))
-- semantic domain
type T_AGRuleItf = JFmtGam ->
                   JGlobViewGam ->
                   JScmGam ->
                   JVarGam ->
                   JViewSetGam ->
                   Opts ->
                   String ->
                   ( PP_Doc,Bool)
data Inh_AGRuleItf = Inh_AGRuleItf {jFmtGam_Inh_AGRuleItf :: JFmtGam,jGlobViewGam_Inh_AGRuleItf :: JGlobViewGam,jScmGam_Inh_AGRuleItf :: JScmGam,jVarGam_Inh_AGRuleItf :: JVarGam,jViewSetGam_Inh_AGRuleItf :: JViewSetGam,opts_Inh_AGRuleItf :: Opts,view_Inh_AGRuleItf :: String}
data Syn_AGRuleItf = Syn_AGRuleItf {ppLaTeX_Syn_AGRuleItf :: PP_Doc,viewIsSel_Syn_AGRuleItf :: Bool}
wrap_AGRuleItf :: T_AGRuleItf ->
                  Inh_AGRuleItf ->
                  Syn_AGRuleItf
wrap_AGRuleItf sem (Inh_AGRuleItf _lhsIjFmtGam _lhsIjGlobViewGam _lhsIjScmGam _lhsIjVarGam _lhsIjViewSetGam _lhsIopts _lhsIview) =
    (let ( _lhsOppLaTeX,_lhsOviewIsSel) = sem _lhsIjFmtGam _lhsIjGlobViewGam _lhsIjScmGam _lhsIjVarGam _lhsIjViewSetGam _lhsIopts _lhsIview
     in  (Syn_AGRuleItf _lhsOppLaTeX _lhsOviewIsSel))
sem_AGRuleItf_AGItf :: T_Rule ->
                       T_AGRuleItf
sem_AGRuleItf_AGItf rule_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOppLaTeX :: PP_Doc
              _lhsOviewIsSel :: Bool
              _ruleOjFmtGam :: JFmtGam
              _ruleOjGlobViewGam :: JGlobViewGam
              _ruleOjScmGam :: JScmGam
              _ruleOjVarGam :: JVarGam
              _ruleOjViewSetGam :: JViewSetGam
              _ruleOopts :: Opts
              _ruleOview :: String
              _ruleIppLaTeX :: PP_Doc
              _ruleIrules :: ([(PP_Doc,Bool,Rule)])
              _ruleIself :: Rule
              _ruleIviewIsSel :: Bool
              _lhsOppLaTeX =
                  _ruleIppLaTeX
              _lhsOviewIsSel =
                  _ruleIviewIsSel
              _ruleOjFmtGam =
                  _lhsIjFmtGam
              _ruleOjGlobViewGam =
                  _lhsIjGlobViewGam
              _ruleOjScmGam =
                  _lhsIjScmGam
              _ruleOjVarGam =
                  _lhsIjVarGam
              _ruleOjViewSetGam =
                  _lhsIjViewSetGam
              _ruleOopts =
                  _lhsIopts
              _ruleOview =
                  _lhsIview
              ( _ruleIppLaTeX,_ruleIrules,_ruleIself,_ruleIviewIsSel) =
                  rule_ _ruleOjFmtGam _ruleOjGlobViewGam _ruleOjScmGam _ruleOjVarGam _ruleOjViewSetGam _ruleOopts _ruleOview
          in  ( _lhsOppLaTeX,_lhsOviewIsSel)))
-- Decl --------------------------------------------------------
data Decl = Decl_Scheme (String) (JExpr) (JExpr) (Views)
          | Decl_Rules (([String])) (String) (ViewSels) (Views) (Rules)
          | Decl_ViewSet (String) (ViewSels)
          | Decl_View (View)
-- cata
sem_Decl :: Decl ->
            T_Decl
sem_Decl (Decl_Scheme _nm _jExpr _jExprRepl _views) =
    (sem_Decl_Scheme _nm (sem_JExpr _jExpr) (sem_JExpr _jExprRepl) (sem_Views _views))
sem_Decl (Decl_Rules _nmL _info _viewSels _views _rules) =
    (sem_Decl_Rules _nmL _info (sem_ViewSels _viewSels) (sem_Views _views) (sem_Rules _rules))
sem_Decl (Decl_ViewSet _nm _viewSels) =
    (sem_Decl_ViewSet _nm (sem_ViewSels _viewSels))
sem_Decl (Decl_View _view) =
    (sem_Decl_View (sem_View _view))
-- semantic domain
type T_Decl = JFmtGam ->
              JGlobViewGam ->
              JScmGam ->
              JViewSetGam ->
              JFmtGam ->
              JGlobViewGam ->
              JScmGam ->
              JVarGam ->
              JViewSetGam ->
              Opts ->
              ( JFmtGam,JGlobViewGam,JScmGam,JViewSetGam,PP_Doc)
sem_Decl_Scheme :: String ->
                   T_JExpr ->
                   T_JExpr ->
                   T_Views ->
                   T_Decl
sem_Decl_Scheme nm_ jExpr_ jExprRepl_ views_ =
    (\ _lhsIgathJFmtGam
       _lhsIgathJGlobViewGam
       _lhsIgathJScmGam
       _lhsIgathJViewSetGam
       _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts ->
         (let _lhsOgathJScmGam :: JScmGam
              _viewsOviewJFmtMp :: ([(String,JFmtGamInfo)])
              _lhsOgathJFmtGam :: JFmtGam
              _jExprOneedToParen :: Bool
              _jExprReplOneedToParen :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOgathJGlobViewGam :: JGlobViewGam
              _lhsOgathJViewSetGam :: JViewSetGam
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOopts :: Opts
              _jExprOview :: String
              _jExprReplOjGlobViewGam :: JGlobViewGam
              _jExprReplOjVarGam :: JVarGam
              _jExprReplOjViewSetGam :: JViewSetGam
              _jExprReplOopts :: Opts
              _jExprReplOview :: String
              _viewsOjFmtGam :: JFmtGam
              _viewsOjGlobViewGam :: JGlobViewGam
              _viewsOjScmGam :: JScmGam
              _viewsOjVarGam :: JVarGam
              _viewsOjViewSetGam :: JViewSetGam
              _viewsOopts :: Opts
              _viewsOschemeTy :: JTy
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              _jExprReplIisEmpty :: Bool
              _jExprReplIjVarGam :: JVarGam
              _jExprReplIppLaTeX :: PP_Doc
              _jExprReplIselL :: ([Maybe (String,PP_Doc)])
              _jExprReplIself :: JExpr
              _jExprReplItxt :: String
              _jExprReplIty :: JTy
              _viewsIviewJFmtMp :: ([(String,JFmtGamInfo)])
              _lhsOgathJScmGam =
                  Map.insert nm_
                      (JScmGamInfo {sgiAllViewNmL= Map.keys _viewJFmtGam, sgiViewNmL= map fst _allJFmtMp})
                      _lhsIgathJScmGam
              _schemeTy =
                  _jExprIty
              _dfltJFmtMp =
                  [("",JFmtGamInfo (jtyUnPPify _schemeTy) _schemeTy _jExprReplIty Map.empty)]
              _viewsOviewJFmtMp =
                  []
              _allJFmtMp =
                  _dfltJFmtMp ++ _viewsIviewJFmtMp
              _viewJFmtGam =
                  fmtAscL2JFmtGam nm_ _allJFmtMp
              _lhsOgathJFmtGam =
                  Map.union _viewJFmtGam _lhsIgathJFmtGam
              _jExprOneedToParen =
                  True
              _jExprReplOneedToParen =
                  True
              _ppScmCmt =
                  vlist
                  . map (\(n,j) -> "%%" >#< n >#< ", template=" >#< ppJTy (fgiFullTy j) >#< ", view=" >#< ppJTy (fgiReplTy j))
                  . Map.toList
                  $ _viewJFmtGam
              _lhsOppLaTeX =
                  _ppScmCmt
              _view =
                  ""
              _lhsOgathJGlobViewGam =
                  _lhsIgathJGlobViewGam
              _lhsOgathJViewSetGam =
                  _lhsIgathJViewSetGam
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _view
              _jExprReplOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprReplOjVarGam =
                  _jExprIjVarGam
              _jExprReplOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprReplOopts =
                  _lhsIopts
              _jExprReplOview =
                  _view
              _viewsOjFmtGam =
                  _lhsIjFmtGam
              _viewsOjGlobViewGam =
                  _lhsIjGlobViewGam
              _viewsOjScmGam =
                  _lhsIjScmGam
              _viewsOjVarGam =
                  _jExprReplIjVarGam
              _viewsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewsOopts =
                  _lhsIopts
              _viewsOschemeTy =
                  _schemeTy
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
              ( _jExprReplIisEmpty,_jExprReplIjVarGam,_jExprReplIppLaTeX,_jExprReplIselL,_jExprReplIself,_jExprReplItxt,_jExprReplIty) =
                  jExprRepl_ _jExprReplOjGlobViewGam _jExprReplOjVarGam _jExprReplOjViewSetGam _jExprReplOneedToParen _jExprReplOopts _jExprReplOview
              ( _viewsIviewJFmtMp) =
                  views_ _viewsOjFmtGam _viewsOjGlobViewGam _viewsOjScmGam _viewsOjVarGam _viewsOjViewSetGam _viewsOopts _viewsOschemeTy _viewsOviewJFmtMp
          in  ( _lhsOgathJFmtGam,_lhsOgathJGlobViewGam,_lhsOgathJScmGam,_lhsOgathJViewSetGam,_lhsOppLaTeX)))
sem_Decl_Rules :: ([String]) ->
                  String ->
                  T_ViewSels ->
                  T_Views ->
                  T_Rules ->
                  T_Decl
sem_Decl_Rules nmL_ info_ viewSels_ views_ rules_ =
    (\ _lhsIgathJFmtGam
       _lhsIgathJGlobViewGam
       _lhsIgathJScmGam
       _lhsIgathJViewSetGam
       _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts ->
         (let _viewsOviewJFmtMp :: ([(String,JFmtGamInfo)])
              _lhsOppLaTeX :: PP_Doc
              _lhsOgathJFmtGam :: JFmtGam
              _lhsOgathJGlobViewGam :: JGlobViewGam
              _lhsOgathJScmGam :: JScmGam
              _lhsOgathJViewSetGam :: JViewSetGam
              _viewSelsOjViewSetGam :: JViewSetGam
              _viewSelsOview :: String
              _viewsOjFmtGam :: JFmtGam
              _viewsOjGlobViewGam :: JGlobViewGam
              _viewsOjScmGam :: JScmGam
              _viewsOjVarGam :: JVarGam
              _viewsOjViewSetGam :: JViewSetGam
              _viewsOopts :: Opts
              _viewsOschemeTy :: JTy
              _rulesOjFmtGam :: JFmtGam
              _rulesOjGlobViewGam :: JGlobViewGam
              _rulesOjScmGam :: JScmGam
              _rulesOjVarGam :: JVarGam
              _rulesOjViewSetGam :: JViewSetGam
              _rulesOopts :: Opts
              _rulesOview :: String
              _viewSelsIisEmpty :: Bool
              _viewSelsIself :: ViewSels
              _viewSelsIviewIsSel :: Bool
              _viewSelsIviewS :: (Set.Set String)
              _viewsIviewJFmtMp :: ([(String,JFmtGamInfo)])
              _rulesIrules :: ([(PP_Doc,Bool,Rule)])
              (_nm,_nmSuff) =
                  hdAndTl nmL_
              _viewsOviewJFmtMp =
                  []
              _jFmtGam =
                  fmtAscL2JFmtGam _nm _viewsIviewJFmtMp `Map.union` _lhsIjFmtGam
              (_schemeTy,_errs) =
                  case Map.lookup _nm _lhsIjFmtGam of
                    Nothing -> (JTy_Any,["RULER error, no scheme for:" >#< _nm])
                    Just fgi -> (fgiTy fgi,[])
              _scmViewNmL =
                  maybe [] sgiViewNmL (Map.lookup _nm _lhsIjScmGam)
              _mkNmBase =
                  \n -> ppDots ([pp (optBaseNm _lhsIopts),n] ++ map pp _nmSuff)
              _mkNmScm =
                  \n -> ppDots [_mkNmBase n,pp "scheme"]
              _mkPP =
                  \vw
                      ->  let scm = _nm ++ vw
                              nBase = _mkNmBase (pp scm)
                              nScm = _mkNmScm (pp scm)
                              varGam
                                = maybe Map.empty fgiVarGam (Map.lookup scm _jFmtGam)
                                  `Map.union` maybe Map.empty gvwgiVarGam (Map.lookup vw _lhsIjGlobViewGam)
                                  `Map.union` _lhsIjVarGam
                              rs = [ (ppDots [nBase,n],h,rPP)
                                   | (n,h,r) <- _rulesIrules
                                   , let (rPP,rSel) = ruleEval r vw _lhsIopts _lhsIjGlobViewGam _lhsIjViewSetGam _lhsIjScmGam _jFmtGam varGam
                                   , rSel
                                   ]
                              ru = concat . map (\(n,h,_) -> [text (if h then "\\qquad" else "\\\\"),mkCmdNmUse n]) $ rs
                              ppSc = mkCmdNmDef nScm (ensureTeXMath . mkInLhs2Tex . ppJTy . fst . mkScmFmt scm fgiFullTy $ _jFmtGam)
                              ppRs = vlist (map (\(n,_,c) -> mkCmdNmDef n c) rs)
                              ppRu = mkCmdNmDef nBase
                                          (    "\\begin{RulesFigure}" >|< ppCurly (mkCmdNmUse nScm) >|< ppCurly (text info_) >|< ppCurly nBase
                                           >-< (if null ru then empty else vlist (tail ru))
                                           >-< "\\end{RulesFigure}"
                                          )
                           in ppRs >-< ppSc >-< ppRu
              _lhsOppLaTeX =
                  vlist [ _mkPP v
                        | v <- _scmViewNmL
                        , Set.null _viewSelsIviewS || v `Set.member` viewExpandNm _lhsIjViewSetGam (Set.toList _viewSelsIviewS)
                        ]
              _view =
                  ""
              _lhsOgathJFmtGam =
                  _lhsIgathJFmtGam
              _lhsOgathJGlobViewGam =
                  _lhsIgathJGlobViewGam
              _lhsOgathJScmGam =
                  _lhsIgathJScmGam
              _lhsOgathJViewSetGam =
                  _lhsIgathJViewSetGam
              _viewSelsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewSelsOview =
                  _view
              _viewsOjFmtGam =
                  _jFmtGam
              _viewsOjGlobViewGam =
                  _lhsIjGlobViewGam
              _viewsOjScmGam =
                  _lhsIjScmGam
              _viewsOjVarGam =
                  _lhsIjVarGam
              _viewsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewsOopts =
                  _lhsIopts
              _viewsOschemeTy =
                  _schemeTy
              _rulesOjFmtGam =
                  _jFmtGam
              _rulesOjGlobViewGam =
                  _lhsIjGlobViewGam
              _rulesOjScmGam =
                  _lhsIjScmGam
              _rulesOjVarGam =
                  _lhsIjVarGam
              _rulesOjViewSetGam =
                  _lhsIjViewSetGam
              _rulesOopts =
                  _lhsIopts
              _rulesOview =
                  _view
              ( _viewSelsIisEmpty,_viewSelsIself,_viewSelsIviewIsSel,_viewSelsIviewS) =
                  viewSels_ _viewSelsOjViewSetGam _viewSelsOview
              ( _viewsIviewJFmtMp) =
                  views_ _viewsOjFmtGam _viewsOjGlobViewGam _viewsOjScmGam _viewsOjVarGam _viewsOjViewSetGam _viewsOopts _viewsOschemeTy _viewsOviewJFmtMp
              ( _rulesIrules) =
                  rules_ _rulesOjFmtGam _rulesOjGlobViewGam _rulesOjScmGam _rulesOjVarGam _rulesOjViewSetGam _rulesOopts _rulesOview
          in  ( _lhsOgathJFmtGam,_lhsOgathJGlobViewGam,_lhsOgathJScmGam,_lhsOgathJViewSetGam,_lhsOppLaTeX)))
sem_Decl_ViewSet :: String ->
                    T_ViewSels ->
                    T_Decl
sem_Decl_ViewSet nm_ viewSels_ =
    (\ _lhsIgathJFmtGam
       _lhsIgathJGlobViewGam
       _lhsIgathJScmGam
       _lhsIgathJViewSetGam
       _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts ->
         (let _lhsOgathJViewSetGam :: JViewSetGam
              _lhsOppLaTeX :: PP_Doc
              _lhsOgathJFmtGam :: JFmtGam
              _lhsOgathJGlobViewGam :: JGlobViewGam
              _lhsOgathJScmGam :: JScmGam
              _viewSelsOjViewSetGam :: JViewSetGam
              _viewSelsOview :: String
              _viewSelsIisEmpty :: Bool
              _viewSelsIself :: ViewSels
              _viewSelsIviewIsSel :: Bool
              _viewSelsIviewS :: (Set.Set String)
              _lhsOgathJViewSetGam =
                  Map.insert nm_
                      (JViewSetGamInfo {vwsgiViewNmS = _viewSelsIviewS})
                      _lhsIgathJViewSetGam
              _view =
                  ""
              _lhsOppLaTeX =
                  empty
              _lhsOgathJFmtGam =
                  _lhsIgathJFmtGam
              _lhsOgathJGlobViewGam =
                  _lhsIgathJGlobViewGam
              _lhsOgathJScmGam =
                  _lhsIgathJScmGam
              _viewSelsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewSelsOview =
                  _view
              ( _viewSelsIisEmpty,_viewSelsIself,_viewSelsIviewIsSel,_viewSelsIviewS) =
                  viewSels_ _viewSelsOjViewSetGam _viewSelsOview
          in  ( _lhsOgathJFmtGam,_lhsOgathJGlobViewGam,_lhsOgathJScmGam,_lhsOgathJViewSetGam,_lhsOppLaTeX)))
sem_Decl_View :: T_View ->
                 T_Decl
sem_Decl_View view_ =
    (\ _lhsIgathJFmtGam
       _lhsIgathJGlobViewGam
       _lhsIgathJScmGam
       _lhsIgathJViewSetGam
       _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts ->
         (let _viewOviewJFmtMp :: ([(String,JFmtGamInfo)])
              _viewOschemeTy :: JTy
              _lhsOgathJGlobViewGam :: JGlobViewGam
              _lhsOppLaTeX :: PP_Doc
              _lhsOgathJFmtGam :: JFmtGam
              _lhsOgathJScmGam :: JScmGam
              _lhsOgathJViewSetGam :: JViewSetGam
              _viewOjFmtGam :: JFmtGam
              _viewOjGlobViewGam :: JGlobViewGam
              _viewOjScmGam :: JScmGam
              _viewOjVarGam :: JVarGam
              _viewOjViewSetGam :: JViewSetGam
              _viewOopts :: Opts
              _viewIjVarGam :: JVarGam
              _viewInmL :: ([String])
              _viewIviewJFmtMp :: ([(String,JFmtGamInfo)])
              _viewOviewJFmtMp =
                  []
              _viewOschemeTy =
                  JTy_Any
              _lhsOgathJGlobViewGam =
                  foldr (\n g
                          -> (\v -> Map.insert n v g) . JGlobViewGamInfo
                             . maybe _viewIjVarGam ((_viewIjVarGam `Map.union`) . gvwgiVarGam)
                             . Map.lookup n $ g
                        )
                        _lhsIgathJGlobViewGam
                        (viewExpandNmL _lhsIjViewSetGam _viewInmL)
              _view =
                  ""
              _lhsOppLaTeX =
                  empty
              _lhsOgathJFmtGam =
                  _lhsIgathJFmtGam
              _lhsOgathJScmGam =
                  _lhsIgathJScmGam
              _lhsOgathJViewSetGam =
                  _lhsIgathJViewSetGam
              _viewOjFmtGam =
                  _lhsIjFmtGam
              _viewOjGlobViewGam =
                  _lhsIjGlobViewGam
              _viewOjScmGam =
                  _lhsIjScmGam
              _viewOjVarGam =
                  _lhsIjVarGam
              _viewOjViewSetGam =
                  _lhsIjViewSetGam
              _viewOopts =
                  _lhsIopts
              ( _viewIjVarGam,_viewInmL,_viewIviewJFmtMp) =
                  view_ _viewOjFmtGam _viewOjGlobViewGam _viewOjScmGam _viewOjVarGam _viewOjViewSetGam _viewOopts _viewOschemeTy _viewOviewJFmtMp
          in  ( _lhsOgathJFmtGam,_lhsOgathJGlobViewGam,_lhsOgathJScmGam,_lhsOgathJViewSetGam,_lhsOppLaTeX)))
-- Decls -------------------------------------------------------
type Decls = [Decl]
-- cata
sem_Decls :: Decls ->
             T_Decls
sem_Decls list =
    (Prelude.foldr sem_Decls_Cons sem_Decls_Nil (Prelude.map sem_Decl list))
-- semantic domain
type T_Decls = JFmtGam ->
               JGlobViewGam ->
               JScmGam ->
               JViewSetGam ->
               JFmtGam ->
               JGlobViewGam ->
               JScmGam ->
               JVarGam ->
               JViewSetGam ->
               Opts ->
               ( JFmtGam,JGlobViewGam,JScmGam,JViewSetGam,PP_Doc)
sem_Decls_Cons :: T_Decl ->
                  T_Decls ->
                  T_Decls
sem_Decls_Cons hd_ tl_ =
    (\ _lhsIgathJFmtGam
       _lhsIgathJGlobViewGam
       _lhsIgathJScmGam
       _lhsIgathJViewSetGam
       _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts ->
         (let _lhsOppLaTeX :: PP_Doc
              _lhsOgathJFmtGam :: JFmtGam
              _lhsOgathJGlobViewGam :: JGlobViewGam
              _lhsOgathJScmGam :: JScmGam
              _lhsOgathJViewSetGam :: JViewSetGam
              _hdOgathJFmtGam :: JFmtGam
              _hdOgathJGlobViewGam :: JGlobViewGam
              _hdOgathJScmGam :: JScmGam
              _hdOgathJViewSetGam :: JViewSetGam
              _hdOjFmtGam :: JFmtGam
              _hdOjGlobViewGam :: JGlobViewGam
              _hdOjScmGam :: JScmGam
              _hdOjVarGam :: JVarGam
              _hdOjViewSetGam :: JViewSetGam
              _hdOopts :: Opts
              _tlOgathJFmtGam :: JFmtGam
              _tlOgathJGlobViewGam :: JGlobViewGam
              _tlOgathJScmGam :: JScmGam
              _tlOgathJViewSetGam :: JViewSetGam
              _tlOjFmtGam :: JFmtGam
              _tlOjGlobViewGam :: JGlobViewGam
              _tlOjScmGam :: JScmGam
              _tlOjVarGam :: JVarGam
              _tlOjViewSetGam :: JViewSetGam
              _tlOopts :: Opts
              _hdIgathJFmtGam :: JFmtGam
              _hdIgathJGlobViewGam :: JGlobViewGam
              _hdIgathJScmGam :: JScmGam
              _hdIgathJViewSetGam :: JViewSetGam
              _hdIppLaTeX :: PP_Doc
              _tlIgathJFmtGam :: JFmtGam
              _tlIgathJGlobViewGam :: JGlobViewGam
              _tlIgathJScmGam :: JScmGam
              _tlIgathJViewSetGam :: JViewSetGam
              _tlIppLaTeX :: PP_Doc
              _lhsOppLaTeX =
                  _hdIppLaTeX >-< _tlIppLaTeX
              _lhsOgathJFmtGam =
                  _tlIgathJFmtGam
              _lhsOgathJGlobViewGam =
                  _tlIgathJGlobViewGam
              _lhsOgathJScmGam =
                  _tlIgathJScmGam
              _lhsOgathJViewSetGam =
                  _tlIgathJViewSetGam
              _hdOgathJFmtGam =
                  _lhsIgathJFmtGam
              _hdOgathJGlobViewGam =
                  _lhsIgathJGlobViewGam
              _hdOgathJScmGam =
                  _lhsIgathJScmGam
              _hdOgathJViewSetGam =
                  _lhsIgathJViewSetGam
              _hdOjFmtGam =
                  _lhsIjFmtGam
              _hdOjGlobViewGam =
                  _lhsIjGlobViewGam
              _hdOjScmGam =
                  _lhsIjScmGam
              _hdOjVarGam =
                  _lhsIjVarGam
              _hdOjViewSetGam =
                  _lhsIjViewSetGam
              _hdOopts =
                  _lhsIopts
              _tlOgathJFmtGam =
                  _hdIgathJFmtGam
              _tlOgathJGlobViewGam =
                  _hdIgathJGlobViewGam
              _tlOgathJScmGam =
                  _hdIgathJScmGam
              _tlOgathJViewSetGam =
                  _hdIgathJViewSetGam
              _tlOjFmtGam =
                  _lhsIjFmtGam
              _tlOjGlobViewGam =
                  _lhsIjGlobViewGam
              _tlOjScmGam =
                  _lhsIjScmGam
              _tlOjVarGam =
                  _lhsIjVarGam
              _tlOjViewSetGam =
                  _lhsIjViewSetGam
              _tlOopts =
                  _lhsIopts
              ( _hdIgathJFmtGam,_hdIgathJGlobViewGam,_hdIgathJScmGam,_hdIgathJViewSetGam,_hdIppLaTeX) =
                  hd_ _hdOgathJFmtGam _hdOgathJGlobViewGam _hdOgathJScmGam _hdOgathJViewSetGam _hdOjFmtGam _hdOjGlobViewGam _hdOjScmGam _hdOjVarGam _hdOjViewSetGam _hdOopts
              ( _tlIgathJFmtGam,_tlIgathJGlobViewGam,_tlIgathJScmGam,_tlIgathJViewSetGam,_tlIppLaTeX) =
                  tl_ _tlOgathJFmtGam _tlOgathJGlobViewGam _tlOgathJScmGam _tlOgathJViewSetGam _tlOjFmtGam _tlOjGlobViewGam _tlOjScmGam _tlOjVarGam _tlOjViewSetGam _tlOopts
          in  ( _lhsOgathJFmtGam,_lhsOgathJGlobViewGam,_lhsOgathJScmGam,_lhsOgathJViewSetGam,_lhsOppLaTeX)))
sem_Decls_Nil :: T_Decls
sem_Decls_Nil =
    (\ _lhsIgathJFmtGam
       _lhsIgathJGlobViewGam
       _lhsIgathJScmGam
       _lhsIgathJViewSetGam
       _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts ->
         (let _lhsOppLaTeX :: PP_Doc
              _lhsOgathJFmtGam :: JFmtGam
              _lhsOgathJGlobViewGam :: JGlobViewGam
              _lhsOgathJScmGam :: JScmGam
              _lhsOgathJViewSetGam :: JViewSetGam
              _lhsOppLaTeX =
                  empty
              _lhsOgathJFmtGam =
                  _lhsIgathJFmtGam
              _lhsOgathJGlobViewGam =
                  _lhsIgathJGlobViewGam
              _lhsOgathJScmGam =
                  _lhsIgathJScmGam
              _lhsOgathJViewSetGam =
                  _lhsIgathJViewSetGam
          in  ( _lhsOgathJFmtGam,_lhsOgathJGlobViewGam,_lhsOgathJScmGam,_lhsOgathJViewSetGam,_lhsOppLaTeX)))
-- JExpr -------------------------------------------------------
data JExpr = JExpr_Op (String) (JExpr) (JExpr) (JExpr)
           | JExpr_AppTop (JExpr)
           | JExpr_Let (String) (JExpr) (JExpr)
           | JExpr_App (JExpr) (JExpr)
           | JExpr_Var (String)
           | JExpr_Str (String)
           | JExpr_StrAsIs (String)
           | JExpr_Paren (JExpr)
           | JExpr_SelTop (JExpr)
           | JExpr_Sel (JExpr) (MbJExpr)
           | JExpr_ViewAs (ViewSels) (JExpr)
           | JExpr_Empty
-- cata
sem_JExpr :: JExpr ->
             T_JExpr
sem_JExpr (JExpr_Op _nm _nmExpr _lExpr _rExpr) =
    (sem_JExpr_Op _nm (sem_JExpr _nmExpr) (sem_JExpr _lExpr) (sem_JExpr _rExpr))
sem_JExpr (JExpr_AppTop _jExpr) =
    (sem_JExpr_AppTop (sem_JExpr _jExpr))
sem_JExpr (JExpr_Let _nm _vExpr _bExpr) =
    (sem_JExpr_Let _nm (sem_JExpr _vExpr) (sem_JExpr _bExpr))
sem_JExpr (JExpr_App _lExpr _rExpr) =
    (sem_JExpr_App (sem_JExpr _lExpr) (sem_JExpr _rExpr))
sem_JExpr (JExpr_Var _nm) =
    (sem_JExpr_Var _nm)
sem_JExpr (JExpr_Str _str) =
    (sem_JExpr_Str _str)
sem_JExpr (JExpr_StrAsIs _str) =
    (sem_JExpr_StrAsIs _str)
sem_JExpr (JExpr_Paren _jExpr) =
    (sem_JExpr_Paren (sem_JExpr _jExpr))
sem_JExpr (JExpr_SelTop _jExpr) =
    (sem_JExpr_SelTop (sem_JExpr _jExpr))
sem_JExpr (JExpr_Sel _jExpr _selMbJExpr) =
    (sem_JExpr_Sel (sem_JExpr _jExpr) (sem_MbJExpr _selMbJExpr))
sem_JExpr (JExpr_ViewAs _viewSels _jExpr) =
    (sem_JExpr_ViewAs (sem_ViewSels _viewSels) (sem_JExpr _jExpr))
sem_JExpr (JExpr_Empty) =
    (sem_JExpr_Empty)
-- semantic domain
type T_JExpr = JGlobViewGam ->
               JVarGam ->
               JViewSetGam ->
               Bool ->
               Opts ->
               String ->
               ( Bool,JVarGam,PP_Doc,([Maybe (String,PP_Doc)]),JExpr,String,JTy)
sem_JExpr_Op :: String ->
                T_JExpr ->
                T_JExpr ->
                T_JExpr ->
                T_JExpr
sem_JExpr_Op nm_ nmExpr_ lExpr_ rExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOty :: JTy
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOtxt :: String
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _nmExprOjGlobViewGam :: JGlobViewGam
              _nmExprOjVarGam :: JVarGam
              _nmExprOjViewSetGam :: JViewSetGam
              _nmExprOneedToParen :: Bool
              _nmExprOopts :: Opts
              _nmExprOview :: String
              _lExprOjGlobViewGam :: JGlobViewGam
              _lExprOjVarGam :: JVarGam
              _lExprOjViewSetGam :: JViewSetGam
              _lExprOneedToParen :: Bool
              _lExprOopts :: Opts
              _lExprOview :: String
              _rExprOjGlobViewGam :: JGlobViewGam
              _rExprOjVarGam :: JVarGam
              _rExprOjViewSetGam :: JViewSetGam
              _rExprOneedToParen :: Bool
              _rExprOopts :: Opts
              _rExprOview :: String
              _nmExprIisEmpty :: Bool
              _nmExprIjVarGam :: JVarGam
              _nmExprIppLaTeX :: PP_Doc
              _nmExprIselL :: ([Maybe (String,PP_Doc)])
              _nmExprIself :: JExpr
              _nmExprItxt :: String
              _nmExprIty :: JTy
              _lExprIisEmpty :: Bool
              _lExprIjVarGam :: JVarGam
              _lExprIppLaTeX :: PP_Doc
              _lExprIselL :: ([Maybe (String,PP_Doc)])
              _lExprIself :: JExpr
              _lExprItxt :: String
              _lExprIty :: JTy
              _rExprIisEmpty :: Bool
              _rExprIjVarGam :: JVarGam
              _rExprIppLaTeX :: PP_Doc
              _rExprIselL :: ([Maybe (String,PP_Doc)])
              _rExprIself :: JExpr
              _rExprItxt :: String
              _rExprIty :: JTy
              _lhsOty =
                  JTy_Op nm_ _nmExprIty _lExprIty _rExprIty
              _lhsOselL =
                  []
              _needToParen =
                  True
              _ppLaTeX =
                  _lExprIppLaTeX >#< mkLhs2TeXSafe nm_ >#< _rExprIppLaTeX
              _lhsOtxt =
                  ""
              _lhsOisEmpty =
                  _nmExprIisEmpty && _lExprIisEmpty && _rExprIisEmpty
              _lhsOppLaTeX =
                  _ppLaTeX
              _self =
                  JExpr_Op nm_ _nmExprIself _lExprIself _rExprIself
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _rExprIjVarGam
              _nmExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _nmExprOjVarGam =
                  _lhsIjVarGam
              _nmExprOjViewSetGam =
                  _lhsIjViewSetGam
              _nmExprOneedToParen =
                  _needToParen
              _nmExprOopts =
                  _lhsIopts
              _nmExprOview =
                  _lhsIview
              _lExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _lExprOjVarGam =
                  _nmExprIjVarGam
              _lExprOjViewSetGam =
                  _lhsIjViewSetGam
              _lExprOneedToParen =
                  _needToParen
              _lExprOopts =
                  _lhsIopts
              _lExprOview =
                  _lhsIview
              _rExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _rExprOjVarGam =
                  _lExprIjVarGam
              _rExprOjViewSetGam =
                  _lhsIjViewSetGam
              _rExprOneedToParen =
                  _needToParen
              _rExprOopts =
                  _lhsIopts
              _rExprOview =
                  _lhsIview
              ( _nmExprIisEmpty,_nmExprIjVarGam,_nmExprIppLaTeX,_nmExprIselL,_nmExprIself,_nmExprItxt,_nmExprIty) =
                  nmExpr_ _nmExprOjGlobViewGam _nmExprOjVarGam _nmExprOjViewSetGam _nmExprOneedToParen _nmExprOopts _nmExprOview
              ( _lExprIisEmpty,_lExprIjVarGam,_lExprIppLaTeX,_lExprIselL,_lExprIself,_lExprItxt,_lExprIty) =
                  lExpr_ _lExprOjGlobViewGam _lExprOjVarGam _lExprOjViewSetGam _lExprOneedToParen _lExprOopts _lExprOview
              ( _rExprIisEmpty,_rExprIjVarGam,_rExprIppLaTeX,_rExprIselL,_rExprIself,_rExprItxt,_rExprIty) =
                  rExpr_ _rExprOjGlobViewGam _rExprOjVarGam _rExprOjViewSetGam _rExprOneedToParen _rExprOopts _rExprOview
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_AppTop :: T_JExpr ->
                    T_JExpr
sem_JExpr_AppTop jExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOty :: JTy
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOtxt :: String
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOneedToParen :: Bool
              _jExprOopts :: Opts
              _jExprOview :: String
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              _lhsOty =
                  JTy_PP _ppLaTeX
              _lhsOselL =
                  []
              _needToParen =
                  True
              _ppLaTeX =
                  _jExprIppLaTeX
              _lhsOtxt =
                  ""
              _lhsOisEmpty =
                  _jExprIisEmpty
              _lhsOppLaTeX =
                  _ppLaTeX
              _self =
                  JExpr_AppTop _jExprIself
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _jExprIjVarGam
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOneedToParen =
                  _needToParen
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _lhsIview
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_Let :: String ->
                 T_JExpr ->
                 T_JExpr ->
                 T_JExpr
sem_JExpr_Let nm_ vExpr_ bExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _bExprOjVarGam :: JVarGam
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOtxt :: String
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _lhsOty :: JTy
              _vExprOjGlobViewGam :: JGlobViewGam
              _vExprOjVarGam :: JVarGam
              _vExprOjViewSetGam :: JViewSetGam
              _vExprOneedToParen :: Bool
              _vExprOopts :: Opts
              _vExprOview :: String
              _bExprOjGlobViewGam :: JGlobViewGam
              _bExprOjViewSetGam :: JViewSetGam
              _bExprOneedToParen :: Bool
              _bExprOopts :: Opts
              _bExprOview :: String
              _vExprIisEmpty :: Bool
              _vExprIjVarGam :: JVarGam
              _vExprIppLaTeX :: PP_Doc
              _vExprIselL :: ([Maybe (String,PP_Doc)])
              _vExprIself :: JExpr
              _vExprItxt :: String
              _vExprIty :: JTy
              _bExprIisEmpty :: Bool
              _bExprIjVarGam :: JVarGam
              _bExprIppLaTeX :: PP_Doc
              _bExprIselL :: ([Maybe (String,PP_Doc)])
              _bExprIself :: JExpr
              _bExprItxt :: String
              _bExprIty :: JTy
              _bExprOjVarGam =
                  Map.insert nm_ (JVarGamInfo _vExprIppLaTeX _vExprIisEmpty) _lhsIjVarGam
              _lhsOselL =
                  []
              _ppLaTeX =
                  _bExprIppLaTeX
              _lhsOisEmpty =
                  _bExprIisEmpty
              _lhsOppLaTeX =
                  _ppLaTeX
              _lhsOtxt =
                  _vExprItxt `const` _bExprItxt
              _self =
                  JExpr_Let nm_ _vExprIself _bExprIself
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _bExprIjVarGam
              _lhsOty =
                  _bExprIty
              _vExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _vExprOjVarGam =
                  _lhsIjVarGam
              _vExprOjViewSetGam =
                  _lhsIjViewSetGam
              _vExprOneedToParen =
                  _lhsIneedToParen
              _vExprOopts =
                  _lhsIopts
              _vExprOview =
                  _lhsIview
              _bExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _bExprOjViewSetGam =
                  _lhsIjViewSetGam
              _bExprOneedToParen =
                  _lhsIneedToParen
              _bExprOopts =
                  _lhsIopts
              _bExprOview =
                  _lhsIview
              ( _vExprIisEmpty,_vExprIjVarGam,_vExprIppLaTeX,_vExprIselL,_vExprIself,_vExprItxt,_vExprIty) =
                  vExpr_ _vExprOjGlobViewGam _vExprOjVarGam _vExprOjViewSetGam _vExprOneedToParen _vExprOopts _vExprOview
              ( _bExprIisEmpty,_bExprIjVarGam,_bExprIppLaTeX,_bExprIselL,_bExprIself,_bExprItxt,_bExprIty) =
                  bExpr_ _bExprOjGlobViewGam _bExprOjVarGam _bExprOjViewSetGam _bExprOneedToParen _bExprOopts _bExprOview
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_App :: T_JExpr ->
                 T_JExpr ->
                 T_JExpr
sem_JExpr_App lExpr_ rExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOtxt :: String
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _lhsOty :: JTy
              _lExprOjGlobViewGam :: JGlobViewGam
              _lExprOjVarGam :: JVarGam
              _lExprOjViewSetGam :: JViewSetGam
              _lExprOneedToParen :: Bool
              _lExprOopts :: Opts
              _lExprOview :: String
              _rExprOjGlobViewGam :: JGlobViewGam
              _rExprOjVarGam :: JVarGam
              _rExprOjViewSetGam :: JViewSetGam
              _rExprOneedToParen :: Bool
              _rExprOopts :: Opts
              _rExprOview :: String
              _lExprIisEmpty :: Bool
              _lExprIjVarGam :: JVarGam
              _lExprIppLaTeX :: PP_Doc
              _lExprIselL :: ([Maybe (String,PP_Doc)])
              _lExprIself :: JExpr
              _lExprItxt :: String
              _lExprIty :: JTy
              _rExprIisEmpty :: Bool
              _rExprIjVarGam :: JVarGam
              _rExprIppLaTeX :: PP_Doc
              _rExprIselL :: ([Maybe (String,PP_Doc)])
              _rExprIself :: JExpr
              _rExprItxt :: String
              _rExprIty :: JTy
              _lhsOselL =
                  []
              _needToParen =
                  True
              _ppLaTeX =
                  _lExprIppLaTeX >#< _rExprIppLaTeX
              _lhsOtxt =
                  ""
              _lhsOisEmpty =
                  _lExprIisEmpty && _rExprIisEmpty
              _lhsOppLaTeX =
                  _ppLaTeX
              _self =
                  JExpr_App _lExprIself _rExprIself
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _rExprIjVarGam
              _lhsOty =
                  _rExprIty
              _lExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _lExprOjVarGam =
                  _lhsIjVarGam
              _lExprOjViewSetGam =
                  _lhsIjViewSetGam
              _lExprOneedToParen =
                  _needToParen
              _lExprOopts =
                  _lhsIopts
              _lExprOview =
                  _lhsIview
              _rExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _rExprOjVarGam =
                  _lExprIjVarGam
              _rExprOjViewSetGam =
                  _lhsIjViewSetGam
              _rExprOneedToParen =
                  _needToParen
              _rExprOopts =
                  _lhsIopts
              _rExprOview =
                  _lhsIview
              ( _lExprIisEmpty,_lExprIjVarGam,_lExprIppLaTeX,_lExprIselL,_lExprIself,_lExprItxt,_lExprIty) =
                  lExpr_ _lExprOjGlobViewGam _lExprOjVarGam _lExprOjViewSetGam _lExprOneedToParen _lExprOopts _lExprOview
              ( _rExprIisEmpty,_rExprIjVarGam,_rExprIppLaTeX,_rExprIselL,_rExprIself,_rExprItxt,_rExprIty) =
                  rExpr_ _rExprOjGlobViewGam _rExprOjVarGam _rExprOjViewSetGam _rExprOneedToParen _rExprOopts _rExprOview
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_Var :: String ->
                 T_JExpr
sem_JExpr_Var nm_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOty :: JTy
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOtxt :: String
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _lhsOty =
                  JTy_Var nm_
              (_ppLaTeX,_isEmpty) =
                  case Map.lookup nm_ _lhsIjVarGam of
                    Nothing -> (text (mkLhs2TeXSafe nm_),False)
                    Just v -> (vgiPP v,vgiIsEmpty v)
              _lhsOselL =
                  []
              _lhsOtxt =
                  nm_
              _lhsOisEmpty =
                  _isEmpty
              _lhsOppLaTeX =
                  _ppLaTeX
              _self =
                  JExpr_Var nm_
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _lhsIjVarGam
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_Str :: String ->
                 T_JExpr
sem_JExpr_Str str_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOty :: JTy
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOtxt :: String
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _lhsOty =
                  JTy_PP _ppLaTeX
              _lhsOselL =
                  []
              _ppLaTeX =
                  switchLaTeXLhs (mkMBox (text str_))
              _lhsOtxt =
                  str_
              _lhsOisEmpty =
                  False
              _lhsOppLaTeX =
                  _ppLaTeX
              _self =
                  JExpr_Str str_
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _lhsIjVarGam
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_StrAsIs :: String ->
                     T_JExpr
sem_JExpr_StrAsIs str_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOty :: JTy
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOtxt :: String
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _lhsOty =
                  JTy_PP _ppLaTeX
              _lhsOselL =
                  []
              _ppLaTeX =
                  text str_
              _lhsOtxt =
                  str_
              _lhsOisEmpty =
                  False
              _lhsOppLaTeX =
                  _ppLaTeX
              _self =
                  JExpr_StrAsIs str_
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _lhsIjVarGam
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_Paren :: T_JExpr ->
                   T_JExpr
sem_JExpr_Paren jExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOty :: JTy
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOtxt :: String
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOneedToParen :: Bool
              _jExprOopts :: Opts
              _jExprOview :: String
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              _lhsOty =
                  JTy_Paren _jExprIty
              _lhsOselL =
                  []
              _needToParen =
                  True
              _ppLaTeX =
                  (if _lhsIneedToParen then ppParens else id) _jExprIppLaTeX
              _lhsOisEmpty =
                  _jExprIisEmpty
              _lhsOppLaTeX =
                  _ppLaTeX
              _lhsOtxt =
                  _jExprItxt
              _self =
                  JExpr_Paren _jExprIself
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _jExprIjVarGam
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOneedToParen =
                  _needToParen
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _lhsIview
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_SelTop :: T_JExpr ->
                    T_JExpr
sem_JExpr_SelTop jExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOty :: JTy
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOtxt :: String
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOneedToParen :: Bool
              _jExprOopts :: Opts
              _jExprOview :: String
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              _lhsOty =
                  JTy_PP _ppLaTeX
              _lhsOselL =
                  []
              _needToParen =
                  True
              _ppLaTeXSel =
                  let sw = (" " >|<) . switchLaTeXLhs
                      over n s = case n of
                                   "_" -> sw (text "\\overline{")
                                   _   -> sw ("\\stackrel{" >|< sw s >|< "}{")
                   in case (_jExprIppLaTeX,reverse _jExprIselL) of
                        (x,[Nothing,Nothing,Just (n3,s3)])
                          -> over n3 s3
                             >|< x
                             >|< sw (text "}")
                        (x,[Nothing,Just (_,s2),Just (n3,s3)])
                          -> over n3 s3
                             >|< x
                             >|< sw ("^{" >|< sw s2 >|< "}}")
                        (x,[Just (_,s1),Nothing,Just (n3,s3)])
                          -> over n3 s3
                             >|< x
                             >|< sw ("_{" >|< sw s1 >|< "}}")
                        (x,[Just (_,s1),Just (_,s2),Just (n3,s3)])
                          -> over n3 s3
                             >|< x
                             >|< sw ("_{" >|< sw s1 >|< "}^{" >|< sw s2 >|< "}}")
                        (x,(Just (_,s1):Just (_,s2):_))
                          -> x >|< sw ("_{" >|< sw s1 >|< "}^{" >|< sw s2 >|< "}")
                        (x,(Nothing:Just (_,s2):_))
                          -> x >|< sw ("^{" >|< sw s2 >|< "}")
                        (x,(Just (_,s1):_))
                          -> x >|< sw ("_{" >|< sw s1 >|< "}")
                        (x,_)
                          -> x
              _ppLaTeX =
                  if _jExprIisEmpty then empty else _ppLaTeXSel
              _lhsOtxt =
                  ""
              _lhsOisEmpty =
                  _jExprIisEmpty
              _lhsOppLaTeX =
                  _ppLaTeX
              _self =
                  JExpr_SelTop _jExprIself
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _jExprIjVarGam
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOneedToParen =
                  _needToParen
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _lhsIview
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_Sel :: T_JExpr ->
                 T_MbJExpr ->
                 T_JExpr
sem_JExpr_Sel jExpr_ selMbJExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOselL :: ([Maybe (String,PP_Doc)])
              _selMbJExprOneedToParen :: Bool
              _jExprOneedToParen :: Bool
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOtxt :: String
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _lhsOty :: JTy
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOopts :: Opts
              _jExprOview :: String
              _selMbJExprOjGlobViewGam :: JGlobViewGam
              _selMbJExprOjVarGam :: JVarGam
              _selMbJExprOjViewSetGam :: JViewSetGam
              _selMbJExprOopts :: Opts
              _selMbJExprOview :: String
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              _selMbJExprImbPPLaTeX :: (Maybe (String,PP_Doc))
              _selMbJExprIself :: MbJExpr
              _lhsOselL =
                  _selMbJExprImbPPLaTeX : _jExprIselL
              _selMbJExprOneedToParen =
                  False
              _jExprOneedToParen =
                  case _selMbJExprImbPPLaTeX of
                    Just ("_",_) -> False
                    _            -> _lhsIneedToParen
              _needToParen =
                  True
              _lhsOisEmpty =
                  _jExprIisEmpty
              _lhsOppLaTeX =
                  _jExprIppLaTeX
              _lhsOtxt =
                  _jExprItxt
              _self =
                  JExpr_Sel _jExprIself _selMbJExprIself
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _jExprIjVarGam
              _lhsOty =
                  _jExprIty
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _lhsIview
              _selMbJExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _selMbJExprOjVarGam =
                  _jExprIjVarGam
              _selMbJExprOjViewSetGam =
                  _lhsIjViewSetGam
              _selMbJExprOopts =
                  _lhsIopts
              _selMbJExprOview =
                  _lhsIview
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
              ( _selMbJExprImbPPLaTeX,_selMbJExprIself) =
                  selMbJExpr_ _selMbJExprOjGlobViewGam _selMbJExprOjVarGam _selMbJExprOjViewSetGam _selMbJExprOneedToParen _selMbJExprOopts _selMbJExprOview
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_ViewAs :: T_ViewSels ->
                    T_JExpr ->
                    T_JExpr
sem_JExpr_ViewAs viewSels_ jExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOtxt :: String
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _lhsOty :: JTy
              _viewSelsOjViewSetGam :: JViewSetGam
              _viewSelsOview :: String
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOneedToParen :: Bool
              _jExprOopts :: Opts
              _jExprOview :: String
              _viewSelsIisEmpty :: Bool
              _viewSelsIself :: ViewSels
              _viewSelsIviewIsSel :: Bool
              _viewSelsIviewS :: (Set.Set String)
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              _lhsOselL =
                  []
              _ppLaTeX =
                  if _viewIsSel then _jExprIppLaTeX else empty
              _viewIsSel =
                  _viewSelsIisEmpty || _lhsIview == "" || _viewSelsIviewIsSel
              _lhsOisEmpty =
                  not _viewIsSel
              _lhsOppLaTeX =
                  _ppLaTeX
              _lhsOtxt =
                  _jExprItxt
              _self =
                  JExpr_ViewAs _viewSelsIself _jExprIself
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _jExprIjVarGam
              _lhsOty =
                  _jExprIty
              _viewSelsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewSelsOview =
                  _lhsIview
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOneedToParen =
                  _lhsIneedToParen
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _lhsIview
              ( _viewSelsIisEmpty,_viewSelsIself,_viewSelsIviewIsSel,_viewSelsIviewS) =
                  viewSels_ _viewSelsOjViewSetGam _viewSelsOview
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
sem_JExpr_Empty :: T_JExpr
sem_JExpr_Empty =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOty :: JTy
              _lhsOselL :: ([Maybe (String,PP_Doc)])
              _lhsOisEmpty :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOtxt :: String
              _lhsOself :: JExpr
              _lhsOjVarGam :: JVarGam
              _lhsOty =
                  JTy_PP _ppLaTeX
              _lhsOselL =
                  []
              _ppLaTeX =
                  empty
              _lhsOisEmpty =
                  True
              _lhsOppLaTeX =
                  _ppLaTeX
              _lhsOtxt =
                  ""
              _self =
                  JExpr_Empty
              _lhsOself =
                  _self
              _lhsOjVarGam =
                  _lhsIjVarGam
          in  ( _lhsOisEmpty,_lhsOjVarGam,_lhsOppLaTeX,_lhsOselL,_lhsOself,_lhsOtxt,_lhsOty)))
-- Judge -------------------------------------------------------
data Judge = Judge_Judge (String) (JExpr)
-- cata
sem_Judge :: Judge ->
             T_Judge
sem_Judge (Judge_Judge _nm _jExpr) =
    (sem_Judge_Judge _nm (sem_JExpr _jExpr))
-- semantic domain
type T_Judge = JFmtGam ->
               JGlobViewGam ->
               JScmGam ->
               JVarGam ->
               JViewSetGam ->
               Opts ->
               String ->
               ( PP_Doc,Judge)
sem_Judge_Judge :: String ->
                   T_JExpr ->
                   T_Judge
sem_Judge_Judge nm_ jExpr_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _jExprOneedToParen :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: Judge
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOopts :: Opts
              _jExprOview :: String
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              (_ty,_errs) =
                  mkScmFmt (nm_ ++ _lhsIview) (const _jExprIty) _lhsIjFmtGam
              _jExprOneedToParen =
                  True
              _lhsOppLaTeX =
                  if null _errs then mkInLhs2Tex (ppJTy _ty) else mkInLhs2Tex (ppListSep "" "" "," _errs)
              _self =
                  Judge_Judge nm_ _jExprIself
              _lhsOself =
                  _self
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _lhsIview
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
          in  ( _lhsOppLaTeX,_lhsOself)))
-- MbJExpr -----------------------------------------------------
data MbJExpr = MbJExpr_Nothing
             | MbJExpr_Just (JExpr)
-- cata
sem_MbJExpr :: MbJExpr ->
               T_MbJExpr
sem_MbJExpr (MbJExpr_Nothing) =
    (sem_MbJExpr_Nothing)
sem_MbJExpr (MbJExpr_Just _jExpr) =
    (sem_MbJExpr_Just (sem_JExpr _jExpr))
-- semantic domain
type T_MbJExpr = JGlobViewGam ->
                 JVarGam ->
                 JViewSetGam ->
                 Bool ->
                 Opts ->
                 String ->
                 ( (Maybe (String,PP_Doc)),MbJExpr)
sem_MbJExpr_Nothing :: T_MbJExpr
sem_MbJExpr_Nothing =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOmbPPLaTeX :: (Maybe (String,PP_Doc))
              _lhsOself :: MbJExpr
              _lhsOmbPPLaTeX =
                  Nothing
              _self =
                  MbJExpr_Nothing
              _lhsOself =
                  _self
          in  ( _lhsOmbPPLaTeX,_lhsOself)))
sem_MbJExpr_Just :: T_JExpr ->
                    T_MbJExpr
sem_MbJExpr_Just jExpr_ =
    (\ _lhsIjGlobViewGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIneedToParen
       _lhsIopts
       _lhsIview ->
         (let _lhsOmbPPLaTeX :: (Maybe (String,PP_Doc))
              _lhsOself :: MbJExpr
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOneedToParen :: Bool
              _jExprOopts :: Opts
              _jExprOview :: String
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              _lhsOmbPPLaTeX =
                  Just (_jExprItxt,_jExprIppLaTeX)
              _self =
                  MbJExpr_Just _jExprIself
              _lhsOself =
                  _self
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOneedToParen =
                  _lhsIneedToParen
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _lhsIview
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
          in  ( _lhsOmbPPLaTeX,_lhsOself)))
-- RExpr -------------------------------------------------------
data RExpr = RExpr_Judge (Judge)
           | RExpr_Cond (JExpr)
-- cata
sem_RExpr :: RExpr ->
             T_RExpr
sem_RExpr (RExpr_Judge _judge) =
    (sem_RExpr_Judge (sem_Judge _judge))
sem_RExpr (RExpr_Cond _jExpr) =
    (sem_RExpr_Cond (sem_JExpr _jExpr))
-- semantic domain
type T_RExpr = JFmtGam ->
               JGlobViewGam ->
               JScmGam ->
               JVarGam ->
               JViewSetGam ->
               Opts ->
               String ->
               ( PP_Doc,RExpr)
sem_RExpr_Judge :: T_Judge ->
                   T_RExpr
sem_RExpr_Judge judge_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOppLaTeX :: PP_Doc
              _lhsOself :: RExpr
              _judgeOjFmtGam :: JFmtGam
              _judgeOjGlobViewGam :: JGlobViewGam
              _judgeOjScmGam :: JScmGam
              _judgeOjVarGam :: JVarGam
              _judgeOjViewSetGam :: JViewSetGam
              _judgeOopts :: Opts
              _judgeOview :: String
              _judgeIppLaTeX :: PP_Doc
              _judgeIself :: Judge
              _lhsOppLaTeX =
                  _judgeIppLaTeX
              _self =
                  RExpr_Judge _judgeIself
              _lhsOself =
                  _self
              _judgeOjFmtGam =
                  _lhsIjFmtGam
              _judgeOjGlobViewGam =
                  _lhsIjGlobViewGam
              _judgeOjScmGam =
                  _lhsIjScmGam
              _judgeOjVarGam =
                  _lhsIjVarGam
              _judgeOjViewSetGam =
                  _lhsIjViewSetGam
              _judgeOopts =
                  _lhsIopts
              _judgeOview =
                  _lhsIview
              ( _judgeIppLaTeX,_judgeIself) =
                  judge_ _judgeOjFmtGam _judgeOjGlobViewGam _judgeOjScmGam _judgeOjVarGam _judgeOjViewSetGam _judgeOopts _judgeOview
          in  ( _lhsOppLaTeX,_lhsOself)))
sem_RExpr_Cond :: T_JExpr ->
                  T_RExpr
sem_RExpr_Cond jExpr_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _jExprOneedToParen :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: RExpr
              _jExprOjGlobViewGam :: JGlobViewGam
              _jExprOjVarGam :: JVarGam
              _jExprOjViewSetGam :: JViewSetGam
              _jExprOopts :: Opts
              _jExprOview :: String
              _jExprIisEmpty :: Bool
              _jExprIjVarGam :: JVarGam
              _jExprIppLaTeX :: PP_Doc
              _jExprIselL :: ([Maybe (String,PP_Doc)])
              _jExprIself :: JExpr
              _jExprItxt :: String
              _jExprIty :: JTy
              _jExprOneedToParen =
                  True
              _ppLaTeX =
                  mkInLhs2Tex _jExprIppLaTeX
              _lhsOppLaTeX =
                  _ppLaTeX
              _self =
                  RExpr_Cond _jExprIself
              _lhsOself =
                  _self
              _jExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprOjVarGam =
                  _lhsIjVarGam
              _jExprOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprOopts =
                  _lhsIopts
              _jExprOview =
                  _lhsIview
              ( _jExprIisEmpty,_jExprIjVarGam,_jExprIppLaTeX,_jExprIselL,_jExprIself,_jExprItxt,_jExprIty) =
                  jExpr_ _jExprOjGlobViewGam _jExprOjVarGam _jExprOjViewSetGam _jExprOneedToParen _jExprOopts _jExprOview
          in  ( _lhsOppLaTeX,_lhsOself)))
-- RExprView ---------------------------------------------------
data RExprView = RExprView_RExpr (RExpr) (ViewSels)
-- cata
sem_RExprView :: RExprView ->
                 T_RExprView
sem_RExprView (RExprView_RExpr _rExpr _viewSels) =
    (sem_RExprView_RExpr (sem_RExpr _rExpr) (sem_ViewSels _viewSels))
-- semantic domain
type T_RExprView = JFmtGam ->
                   JGlobViewGam ->
                   JScmGam ->
                   JVarGam ->
                   JViewSetGam ->
                   Opts ->
                   String ->
                   ( PP_Doc,RExprView,Bool)
sem_RExprView_RExpr :: T_RExpr ->
                       T_ViewSels ->
                       T_RExprView
sem_RExprView_RExpr rExpr_ viewSels_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOviewIsSel :: Bool
              _lhsOppLaTeX :: PP_Doc
              _lhsOself :: RExprView
              _rExprOjFmtGam :: JFmtGam
              _rExprOjGlobViewGam :: JGlobViewGam
              _rExprOjScmGam :: JScmGam
              _rExprOjVarGam :: JVarGam
              _rExprOjViewSetGam :: JViewSetGam
              _rExprOopts :: Opts
              _rExprOview :: String
              _viewSelsOjViewSetGam :: JViewSetGam
              _viewSelsOview :: String
              _rExprIppLaTeX :: PP_Doc
              _rExprIself :: RExpr
              _viewSelsIisEmpty :: Bool
              _viewSelsIself :: ViewSels
              _viewSelsIviewIsSel :: Bool
              _viewSelsIviewS :: (Set.Set String)
              _lhsOviewIsSel =
                  _viewSelsIisEmpty || _lhsIview == "" || _viewSelsIviewIsSel
              _lhsOppLaTeX =
                  _rExprIppLaTeX
              _self =
                  RExprView_RExpr _rExprIself _viewSelsIself
              _lhsOself =
                  _self
              _rExprOjFmtGam =
                  _lhsIjFmtGam
              _rExprOjGlobViewGam =
                  _lhsIjGlobViewGam
              _rExprOjScmGam =
                  _lhsIjScmGam
              _rExprOjVarGam =
                  _lhsIjVarGam
              _rExprOjViewSetGam =
                  _lhsIjViewSetGam
              _rExprOopts =
                  _lhsIopts
              _rExprOview =
                  _lhsIview
              _viewSelsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewSelsOview =
                  _lhsIview
              ( _rExprIppLaTeX,_rExprIself) =
                  rExpr_ _rExprOjFmtGam _rExprOjGlobViewGam _rExprOjScmGam _rExprOjVarGam _rExprOjViewSetGam _rExprOopts _rExprOview
              ( _viewSelsIisEmpty,_viewSelsIself,_viewSelsIviewIsSel,_viewSelsIviewS) =
                  viewSels_ _viewSelsOjViewSetGam _viewSelsOview
          in  ( _lhsOppLaTeX,_lhsOself,_lhsOviewIsSel)))
-- RExprViews --------------------------------------------------
type RExprViews = [RExprView]
-- cata
sem_RExprViews :: RExprViews ->
                  T_RExprViews
sem_RExprViews list =
    (Prelude.foldr sem_RExprViews_Cons sem_RExprViews_Nil (Prelude.map sem_RExprView list))
-- semantic domain
type T_RExprViews = JFmtGam ->
                    JGlobViewGam ->
                    JScmGam ->
                    JVarGam ->
                    JViewSetGam ->
                    Opts ->
                    String ->
                    ( PP_DocL,RExprViews)
sem_RExprViews_Cons :: T_RExprView ->
                       T_RExprViews ->
                       T_RExprViews
sem_RExprViews_Cons hd_ tl_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOppLaTeXL :: PP_DocL
              _lhsOself :: RExprViews
              _hdOjFmtGam :: JFmtGam
              _hdOjGlobViewGam :: JGlobViewGam
              _hdOjScmGam :: JScmGam
              _hdOjVarGam :: JVarGam
              _hdOjViewSetGam :: JViewSetGam
              _hdOopts :: Opts
              _hdOview :: String
              _tlOjFmtGam :: JFmtGam
              _tlOjGlobViewGam :: JGlobViewGam
              _tlOjScmGam :: JScmGam
              _tlOjVarGam :: JVarGam
              _tlOjViewSetGam :: JViewSetGam
              _tlOopts :: Opts
              _tlOview :: String
              _hdIppLaTeX :: PP_Doc
              _hdIself :: RExprView
              _hdIviewIsSel :: Bool
              _tlIppLaTeXL :: PP_DocL
              _tlIself :: RExprViews
              _lhsOppLaTeXL =
                  if _hdIviewIsSel then _hdIppLaTeX : _tlIppLaTeXL else _tlIppLaTeXL
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOjFmtGam =
                  _lhsIjFmtGam
              _hdOjGlobViewGam =
                  _lhsIjGlobViewGam
              _hdOjScmGam =
                  _lhsIjScmGam
              _hdOjVarGam =
                  _lhsIjVarGam
              _hdOjViewSetGam =
                  _lhsIjViewSetGam
              _hdOopts =
                  _lhsIopts
              _hdOview =
                  _lhsIview
              _tlOjFmtGam =
                  _lhsIjFmtGam
              _tlOjGlobViewGam =
                  _lhsIjGlobViewGam
              _tlOjScmGam =
                  _lhsIjScmGam
              _tlOjVarGam =
                  _lhsIjVarGam
              _tlOjViewSetGam =
                  _lhsIjViewSetGam
              _tlOopts =
                  _lhsIopts
              _tlOview =
                  _lhsIview
              ( _hdIppLaTeX,_hdIself,_hdIviewIsSel) =
                  hd_ _hdOjFmtGam _hdOjGlobViewGam _hdOjScmGam _hdOjVarGam _hdOjViewSetGam _hdOopts _hdOview
              ( _tlIppLaTeXL,_tlIself) =
                  tl_ _tlOjFmtGam _tlOjGlobViewGam _tlOjScmGam _tlOjVarGam _tlOjViewSetGam _tlOopts _tlOview
          in  ( _lhsOppLaTeXL,_lhsOself)))
sem_RExprViews_Nil :: T_RExprViews
sem_RExprViews_Nil =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOppLaTeXL :: PP_DocL
              _lhsOself :: RExprViews
              _lhsOppLaTeXL =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOppLaTeXL,_lhsOself)))
-- Rule --------------------------------------------------------
data Rule = Rule_Rule (Bool) (String) (ViewSels) (RExprViews) (RExprViews)
          | Rule_RuleUse (Bool) (String) (ViewSels) (([String]))
-- cata
sem_Rule :: Rule ->
            T_Rule
sem_Rule (Rule_Rule _layoutHor _nm _viewSels _pre _post) =
    (sem_Rule_Rule _layoutHor _nm (sem_ViewSels _viewSels) (sem_RExprViews _pre) (sem_RExprViews _post))
sem_Rule (Rule_RuleUse _layoutHor _nm _viewSels _aliasNmL) =
    (sem_Rule_RuleUse _layoutHor _nm (sem_ViewSels _viewSels) _aliasNmL)
-- semantic domain
type T_Rule = JFmtGam ->
              JGlobViewGam ->
              JScmGam ->
              JVarGam ->
              JViewSetGam ->
              Opts ->
              String ->
              ( PP_Doc,([(PP_Doc,Bool,Rule)]),Rule,Bool)
sem_Rule_Rule :: Bool ->
                 String ->
                 T_ViewSels ->
                 T_RExprViews ->
                 T_RExprViews ->
                 T_Rule
sem_Rule_Rule layoutHor_ nm_ viewSels_ pre_ post_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOppLaTeX :: PP_Doc
              _lhsOrules :: ([(PP_Doc,Bool,Rule)])
              _lhsOviewIsSel :: Bool
              _lhsOself :: Rule
              _viewSelsOjViewSetGam :: JViewSetGam
              _viewSelsOview :: String
              _preOjFmtGam :: JFmtGam
              _preOjGlobViewGam :: JGlobViewGam
              _preOjScmGam :: JScmGam
              _preOjVarGam :: JVarGam
              _preOjViewSetGam :: JViewSetGam
              _preOopts :: Opts
              _preOview :: String
              _postOjFmtGam :: JFmtGam
              _postOjGlobViewGam :: JGlobViewGam
              _postOjScmGam :: JScmGam
              _postOjVarGam :: JVarGam
              _postOjViewSetGam :: JViewSetGam
              _postOopts :: Opts
              _postOview :: String
              _viewSelsIisEmpty :: Bool
              _viewSelsIself :: ViewSels
              _viewSelsIviewIsSel :: Bool
              _viewSelsIviewS :: (Set.Set String)
              _preIppLaTeXL :: PP_DocL
              _preIself :: RExprViews
              _postIppLaTeXL :: PP_DocL
              _postIself :: RExprViews
              _lhsOppLaTeX =
                  "\\ehinfrule" >|< ppCurly (mkLaTeXNm nm_) >|< ppCurly _lhsIview
                  >-< ppListSepVV "{%" "}" "\\\\" _preIppLaTeXL
                  >-< ppListSepVV "{%" "}" "\\\\"  _postIppLaTeXL
              _lhsOrules =
                  [(pp (mkLaTeXNm nm_),layoutHor_,_self)]
              _lhsOviewIsSel =
                  _viewSelsIisEmpty || _lhsIview == "" || _viewSelsIviewIsSel
              _self =
                  Rule_Rule layoutHor_ nm_ _viewSelsIself _preIself _postIself
              _lhsOself =
                  _self
              _viewSelsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewSelsOview =
                  _lhsIview
              _preOjFmtGam =
                  _lhsIjFmtGam
              _preOjGlobViewGam =
                  _lhsIjGlobViewGam
              _preOjScmGam =
                  _lhsIjScmGam
              _preOjVarGam =
                  _lhsIjVarGam
              _preOjViewSetGam =
                  _lhsIjViewSetGam
              _preOopts =
                  _lhsIopts
              _preOview =
                  _lhsIview
              _postOjFmtGam =
                  _lhsIjFmtGam
              _postOjGlobViewGam =
                  _lhsIjGlobViewGam
              _postOjScmGam =
                  _lhsIjScmGam
              _postOjVarGam =
                  _lhsIjVarGam
              _postOjViewSetGam =
                  _lhsIjViewSetGam
              _postOopts =
                  _lhsIopts
              _postOview =
                  _lhsIview
              ( _viewSelsIisEmpty,_viewSelsIself,_viewSelsIviewIsSel,_viewSelsIviewS) =
                  viewSels_ _viewSelsOjViewSetGam _viewSelsOview
              ( _preIppLaTeXL,_preIself) =
                  pre_ _preOjFmtGam _preOjGlobViewGam _preOjScmGam _preOjVarGam _preOjViewSetGam _preOopts _preOview
              ( _postIppLaTeXL,_postIself) =
                  post_ _postOjFmtGam _postOjGlobViewGam _postOjScmGam _postOjVarGam _postOjViewSetGam _postOopts _postOview
          in  ( _lhsOppLaTeX,_lhsOrules,_lhsOself,_lhsOviewIsSel)))
sem_Rule_RuleUse :: Bool ->
                    String ->
                    T_ViewSels ->
                    ([String]) ->
                    T_Rule
sem_Rule_RuleUse layoutHor_ nm_ viewSels_ aliasNmL_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOppLaTeX :: PP_Doc
              _lhsOrules :: ([(PP_Doc,Bool,Rule)])
              _lhsOviewIsSel :: Bool
              _lhsOself :: Rule
              _viewSelsOjViewSetGam :: JViewSetGam
              _viewSelsOview :: String
              _viewSelsIisEmpty :: Bool
              _viewSelsIself :: ViewSels
              _viewSelsIviewIsSel :: Bool
              _viewSelsIviewS :: (Set.Set String)
              (_aliasNm,_aliasNmSuff) =
                  hdAndTl aliasNmL_
              _lhsOppLaTeX =
                  mkCmdNmUse (ppDots (optBaseNm _lhsIopts : mkLaTeXNm (_aliasNm ++ _lhsIview) : map mkLaTeXNm _aliasNmSuff))
              _lhsOrules =
                  [(pp (mkLaTeXNm nm_),layoutHor_,_self)]
              _lhsOviewIsSel =
                  _viewSelsIisEmpty || _lhsIview == "" || _viewSelsIviewIsSel
              _self =
                  Rule_RuleUse layoutHor_ nm_ _viewSelsIself aliasNmL_
              _lhsOself =
                  _self
              _viewSelsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewSelsOview =
                  _lhsIview
              ( _viewSelsIisEmpty,_viewSelsIself,_viewSelsIviewIsSel,_viewSelsIviewS) =
                  viewSels_ _viewSelsOjViewSetGam _viewSelsOview
          in  ( _lhsOppLaTeX,_lhsOrules,_lhsOself,_lhsOviewIsSel)))
-- Rules -------------------------------------------------------
type Rules = [Rule]
-- cata
sem_Rules :: Rules ->
             T_Rules
sem_Rules list =
    (Prelude.foldr sem_Rules_Cons sem_Rules_Nil (Prelude.map sem_Rule list))
-- semantic domain
type T_Rules = JFmtGam ->
               JGlobViewGam ->
               JScmGam ->
               JVarGam ->
               JViewSetGam ->
               Opts ->
               String ->
               ( ([(PP_Doc,Bool,Rule)]))
sem_Rules_Cons :: T_Rule ->
                  T_Rules ->
                  T_Rules
sem_Rules_Cons hd_ tl_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOrules :: ([(PP_Doc,Bool,Rule)])
              _hdOjFmtGam :: JFmtGam
              _hdOjGlobViewGam :: JGlobViewGam
              _hdOjScmGam :: JScmGam
              _hdOjVarGam :: JVarGam
              _hdOjViewSetGam :: JViewSetGam
              _hdOopts :: Opts
              _hdOview :: String
              _tlOjFmtGam :: JFmtGam
              _tlOjGlobViewGam :: JGlobViewGam
              _tlOjScmGam :: JScmGam
              _tlOjVarGam :: JVarGam
              _tlOjViewSetGam :: JViewSetGam
              _tlOopts :: Opts
              _tlOview :: String
              _hdIppLaTeX :: PP_Doc
              _hdIrules :: ([(PP_Doc,Bool,Rule)])
              _hdIself :: Rule
              _hdIviewIsSel :: Bool
              _tlIrules :: ([(PP_Doc,Bool,Rule)])
              _lhsOrules =
                  _hdIrules ++ _tlIrules
              _hdOjFmtGam =
                  _lhsIjFmtGam
              _hdOjGlobViewGam =
                  _lhsIjGlobViewGam
              _hdOjScmGam =
                  _lhsIjScmGam
              _hdOjVarGam =
                  _lhsIjVarGam
              _hdOjViewSetGam =
                  _lhsIjViewSetGam
              _hdOopts =
                  _lhsIopts
              _hdOview =
                  _lhsIview
              _tlOjFmtGam =
                  _lhsIjFmtGam
              _tlOjGlobViewGam =
                  _lhsIjGlobViewGam
              _tlOjScmGam =
                  _lhsIjScmGam
              _tlOjVarGam =
                  _lhsIjVarGam
              _tlOjViewSetGam =
                  _lhsIjViewSetGam
              _tlOopts =
                  _lhsIopts
              _tlOview =
                  _lhsIview
              ( _hdIppLaTeX,_hdIrules,_hdIself,_hdIviewIsSel) =
                  hd_ _hdOjFmtGam _hdOjGlobViewGam _hdOjScmGam _hdOjVarGam _hdOjViewSetGam _hdOopts _hdOview
              ( _tlIrules) =
                  tl_ _tlOjFmtGam _tlOjGlobViewGam _tlOjScmGam _tlOjVarGam _tlOjViewSetGam _tlOopts _tlOview
          in  ( _lhsOrules)))
sem_Rules_Nil :: T_Rules
sem_Rules_Nil =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIview ->
         (let _lhsOrules :: ([(PP_Doc,Bool,Rule)])
              _lhsOrules =
                  []
          in  ( _lhsOrules)))
-- View --------------------------------------------------------
data View = View_View (ViewSels) (JExpr)
-- cata
sem_View :: View ->
            T_View
sem_View (View_View _viewSels _jExprRepl) =
    (sem_View_View (sem_ViewSels _viewSels) (sem_JExpr _jExprRepl))
-- semantic domain
type T_View = JFmtGam ->
              JGlobViewGam ->
              JScmGam ->
              JVarGam ->
              JViewSetGam ->
              Opts ->
              JTy ->
              ([(String,JFmtGamInfo)]) ->
              ( JVarGam,([String]),([(String,JFmtGamInfo)]))
sem_View_View :: T_ViewSels ->
                 T_JExpr ->
                 T_View
sem_View_View viewSels_ jExprRepl_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIschemeTy
       _lhsIviewJFmtMp ->
         (let _jExprReplOjVarGam :: JVarGam
              _lhsOviewJFmtMp :: ([(String,JFmtGamInfo)])
              _jExprReplOneedToParen :: Bool
              _lhsOjVarGam :: JVarGam
              _lhsOnmL :: ([String])
              _viewSelsOjViewSetGam :: JViewSetGam
              _viewSelsOview :: String
              _jExprReplOjGlobViewGam :: JGlobViewGam
              _jExprReplOjViewSetGam :: JViewSetGam
              _jExprReplOopts :: Opts
              _jExprReplOview :: String
              _viewSelsIisEmpty :: Bool
              _viewSelsIself :: ViewSels
              _viewSelsIviewIsSel :: Bool
              _viewSelsIviewS :: (Set.Set String)
              _jExprReplIisEmpty :: Bool
              _jExprReplIjVarGam :: JVarGam
              _jExprReplIppLaTeX :: PP_Doc
              _jExprReplIselL :: ([Maybe (String,PP_Doc)])
              _jExprReplIself :: JExpr
              _jExprReplItxt :: String
              _jExprReplIty :: JTy
              _jExprReplOjVarGam =
                  Map.empty
              _lhsOviewJFmtMp =
                  zip (viewExpandNmL _lhsIjViewSetGam _nmL) (repeat (JFmtGamInfo (jtyUnPPify _lhsIschemeTy) _lhsIschemeTy _jExprReplIty _jExprReplIjVarGam))
                  ++ _lhsIviewJFmtMp
              _jExprReplOneedToParen =
                  True
              _view =
                  ""
              _nmL =
                  Set.toList _viewSelsIviewS
              _lhsOjVarGam =
                  _jExprReplIjVarGam
              _lhsOnmL =
                  _nmL
              _viewSelsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewSelsOview =
                  _view
              _jExprReplOjGlobViewGam =
                  _lhsIjGlobViewGam
              _jExprReplOjViewSetGam =
                  _lhsIjViewSetGam
              _jExprReplOopts =
                  _lhsIopts
              _jExprReplOview =
                  _view
              ( _viewSelsIisEmpty,_viewSelsIself,_viewSelsIviewIsSel,_viewSelsIviewS) =
                  viewSels_ _viewSelsOjViewSetGam _viewSelsOview
              ( _jExprReplIisEmpty,_jExprReplIjVarGam,_jExprReplIppLaTeX,_jExprReplIselL,_jExprReplIself,_jExprReplItxt,_jExprReplIty) =
                  jExprRepl_ _jExprReplOjGlobViewGam _jExprReplOjVarGam _jExprReplOjViewSetGam _jExprReplOneedToParen _jExprReplOopts _jExprReplOview
          in  ( _lhsOjVarGam,_lhsOnmL,_lhsOviewJFmtMp)))
-- ViewSel -----------------------------------------------------
data ViewSel = ViewSel_One (String)
             | ViewSel_Many (ViewSels)
-- cata
sem_ViewSel :: ViewSel ->
               T_ViewSel
sem_ViewSel (ViewSel_One _nm) =
    (sem_ViewSel_One _nm)
sem_ViewSel (ViewSel_Many _viewSels) =
    (sem_ViewSel_Many (sem_ViewSels _viewSels))
-- semantic domain
type T_ViewSel = JViewSetGam ->
                 String ->
                 ( ViewSel,Bool,(Set.Set String))
sem_ViewSel_One :: String ->
                   T_ViewSel
sem_ViewSel_One nm_ =
    (\ _lhsIjViewSetGam
       _lhsIview ->
         (let _lhsOviewIsSel :: Bool
              _lhsOviewS :: (Set.Set String)
              _lhsOself :: ViewSel
              _lhsOviewIsSel =
                  viewIsInSel _lhsIjViewSetGam nm_ _lhsIview
              _lhsOviewS =
                  Set.singleton nm_
              _self =
                  ViewSel_One nm_
              _lhsOself =
                  _self
          in  ( _lhsOself,_lhsOviewIsSel,_lhsOviewS)))
sem_ViewSel_Many :: T_ViewSels ->
                    T_ViewSel
sem_ViewSel_Many viewSels_ =
    (\ _lhsIjViewSetGam
       _lhsIview ->
         (let _lhsOviewIsSel :: Bool
              _lhsOviewS :: (Set.Set String)
              _lhsOself :: ViewSel
              _viewSelsOjViewSetGam :: JViewSetGam
              _viewSelsOview :: String
              _viewSelsIisEmpty :: Bool
              _viewSelsIself :: ViewSels
              _viewSelsIviewIsSel :: Bool
              _viewSelsIviewS :: (Set.Set String)
              _lhsOviewIsSel =
                  _viewSelsIviewIsSel
              _lhsOviewS =
                  _viewSelsIviewS
              _self =
                  ViewSel_Many _viewSelsIself
              _lhsOself =
                  _self
              _viewSelsOjViewSetGam =
                  _lhsIjViewSetGam
              _viewSelsOview =
                  _lhsIview
              ( _viewSelsIisEmpty,_viewSelsIself,_viewSelsIviewIsSel,_viewSelsIviewS) =
                  viewSels_ _viewSelsOjViewSetGam _viewSelsOview
          in  ( _lhsOself,_lhsOviewIsSel,_lhsOviewS)))
-- ViewSels ----------------------------------------------------
type ViewSels = [ViewSel]
-- cata
sem_ViewSels :: ViewSels ->
                T_ViewSels
sem_ViewSels list =
    (Prelude.foldr sem_ViewSels_Cons sem_ViewSels_Nil (Prelude.map sem_ViewSel list))
-- semantic domain
type T_ViewSels = JViewSetGam ->
                  String ->
                  ( Bool,ViewSels,Bool,(Set.Set String))
sem_ViewSels_Cons :: T_ViewSel ->
                     T_ViewSels ->
                     T_ViewSels
sem_ViewSels_Cons hd_ tl_ =
    (\ _lhsIjViewSetGam
       _lhsIview ->
         (let _lhsOisEmpty :: Bool
              _lhsOviewIsSel :: Bool
              _lhsOviewS :: (Set.Set String)
              _lhsOself :: ViewSels
              _hdOjViewSetGam :: JViewSetGam
              _hdOview :: String
              _tlOjViewSetGam :: JViewSetGam
              _tlOview :: String
              _hdIself :: ViewSel
              _hdIviewIsSel :: Bool
              _hdIviewS :: (Set.Set String)
              _tlIisEmpty :: Bool
              _tlIself :: ViewSels
              _tlIviewIsSel :: Bool
              _tlIviewS :: (Set.Set String)
              _lhsOisEmpty =
                  False
              _lhsOviewIsSel =
                  _hdIviewIsSel || _tlIviewIsSel
              _lhsOviewS =
                  _hdIviewS `Set.union` _tlIviewS
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOjViewSetGam =
                  _lhsIjViewSetGam
              _hdOview =
                  _lhsIview
              _tlOjViewSetGam =
                  _lhsIjViewSetGam
              _tlOview =
                  _lhsIview
              ( _hdIself,_hdIviewIsSel,_hdIviewS) =
                  hd_ _hdOjViewSetGam _hdOview
              ( _tlIisEmpty,_tlIself,_tlIviewIsSel,_tlIviewS) =
                  tl_ _tlOjViewSetGam _tlOview
          in  ( _lhsOisEmpty,_lhsOself,_lhsOviewIsSel,_lhsOviewS)))
sem_ViewSels_Nil :: T_ViewSels
sem_ViewSels_Nil =
    (\ _lhsIjViewSetGam
       _lhsIview ->
         (let _lhsOisEmpty :: Bool
              _lhsOviewIsSel :: Bool
              _lhsOviewS :: (Set.Set String)
              _lhsOself :: ViewSels
              _lhsOisEmpty =
                  True
              _lhsOviewIsSel =
                  False
              _lhsOviewS =
                  Set.empty
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOisEmpty,_lhsOself,_lhsOviewIsSel,_lhsOviewS)))
-- Views -------------------------------------------------------
type Views = [View]
-- cata
sem_Views :: Views ->
             T_Views
sem_Views list =
    (Prelude.foldr sem_Views_Cons sem_Views_Nil (Prelude.map sem_View list))
-- semantic domain
type T_Views = JFmtGam ->
               JGlobViewGam ->
               JScmGam ->
               JVarGam ->
               JViewSetGam ->
               Opts ->
               JTy ->
               ([(String,JFmtGamInfo)]) ->
               ( ([(String,JFmtGamInfo)]))
sem_Views_Cons :: T_View ->
                  T_Views ->
                  T_Views
sem_Views_Cons hd_ tl_ =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIschemeTy
       _lhsIviewJFmtMp ->
         (let _lhsOviewJFmtMp :: ([(String,JFmtGamInfo)])
              _hdOjFmtGam :: JFmtGam
              _hdOjGlobViewGam :: JGlobViewGam
              _hdOjScmGam :: JScmGam
              _hdOjVarGam :: JVarGam
              _hdOjViewSetGam :: JViewSetGam
              _hdOopts :: Opts
              _hdOschemeTy :: JTy
              _hdOviewJFmtMp :: ([(String,JFmtGamInfo)])
              _tlOjFmtGam :: JFmtGam
              _tlOjGlobViewGam :: JGlobViewGam
              _tlOjScmGam :: JScmGam
              _tlOjVarGam :: JVarGam
              _tlOjViewSetGam :: JViewSetGam
              _tlOopts :: Opts
              _tlOschemeTy :: JTy
              _tlOviewJFmtMp :: ([(String,JFmtGamInfo)])
              _hdIjVarGam :: JVarGam
              _hdInmL :: ([String])
              _hdIviewJFmtMp :: ([(String,JFmtGamInfo)])
              _tlIviewJFmtMp :: ([(String,JFmtGamInfo)])
              _lhsOviewJFmtMp =
                  _tlIviewJFmtMp
              _hdOjFmtGam =
                  _lhsIjFmtGam
              _hdOjGlobViewGam =
                  _lhsIjGlobViewGam
              _hdOjScmGam =
                  _lhsIjScmGam
              _hdOjVarGam =
                  _lhsIjVarGam
              _hdOjViewSetGam =
                  _lhsIjViewSetGam
              _hdOopts =
                  _lhsIopts
              _hdOschemeTy =
                  _lhsIschemeTy
              _hdOviewJFmtMp =
                  _lhsIviewJFmtMp
              _tlOjFmtGam =
                  _lhsIjFmtGam
              _tlOjGlobViewGam =
                  _lhsIjGlobViewGam
              _tlOjScmGam =
                  _lhsIjScmGam
              _tlOjVarGam =
                  _hdIjVarGam
              _tlOjViewSetGam =
                  _lhsIjViewSetGam
              _tlOopts =
                  _lhsIopts
              _tlOschemeTy =
                  _lhsIschemeTy
              _tlOviewJFmtMp =
                  _hdIviewJFmtMp
              ( _hdIjVarGam,_hdInmL,_hdIviewJFmtMp) =
                  hd_ _hdOjFmtGam _hdOjGlobViewGam _hdOjScmGam _hdOjVarGam _hdOjViewSetGam _hdOopts _hdOschemeTy _hdOviewJFmtMp
              ( _tlIviewJFmtMp) =
                  tl_ _tlOjFmtGam _tlOjGlobViewGam _tlOjScmGam _tlOjVarGam _tlOjViewSetGam _tlOopts _tlOschemeTy _tlOviewJFmtMp
          in  ( _lhsOviewJFmtMp)))
sem_Views_Nil :: T_Views
sem_Views_Nil =
    (\ _lhsIjFmtGam
       _lhsIjGlobViewGam
       _lhsIjScmGam
       _lhsIjVarGam
       _lhsIjViewSetGam
       _lhsIopts
       _lhsIschemeTy
       _lhsIviewJFmtMp ->
         (let _lhsOviewJFmtMp :: ([(String,JFmtGamInfo)])
              _lhsOviewJFmtMp =
                  _lhsIviewJFmtMp
          in  ( _lhsOviewJFmtMp)))