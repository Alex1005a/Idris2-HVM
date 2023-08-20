module Main

import Core.Context

import Compiler.Common
import Compiler.CompileExpr

import Idris.Driver
import Idris.Syntax

import Data.Vect
import Data.String

import Libraries.Utils.Path
import Libraries.Data.String.Builder

import Protocol.Hex

import System

-- Type, arity and constructor name
ConsInfo = List (Name, Nat, Name)

predefined : Builder
predefined = 
  """
  (IfElse 1 exp _) = exp
  (IfElse _ _ exp) = exp

  (Cond sc (Data.List.cons (Case c exp) next)) = (IfElse (== sc c) exp (Cond sc next))
  (Cond _ (Data.List.cons (Default exp) _)) = exp 

  (String.concat Data.String.nil         ys) = ys
  (String.concat (Data.String.cons x xs) ys) = (Data.String.cons x (String.concat xs ys))

  (ToString 0) = "0"
  (ToString 1) = "1"
  (ToString 2) = "2"
  (ToString 3) = "3"
  (ToString 4) = "4"
  (ToString 5) = "5"
  (ToString 6) = "6"
  (ToString 7) = "7"
  (ToString 8) = "8"
  (ToString 9) = "9"
  (ToString num) = (String.concat (ToString (/ num 10)) (ToString (% num 10)))

  (StrHead (Data.String.cons x _)) = x

  (StrTail (Data.String.cons _ xs)) = xs

  (StrLen (Data.String.cons _ xs)) = (+ 1 (StrLen xs))
  (StrLen Data.String.nil) = 0

  (StrRev str (Data.String.cons x xs)) = (StrRev (Data.String.cons x str) xs)
  (StrRev str Data.String.nil) = str

  (StrIdx (Data.String.cons x xs) 0) = x
  (StrIdx (Data.String.cons _ xs) idx) = (StrIdx xs (- idx 1))

  (StrSkip 0 str) = str
  (StrSkip n Data.String.nil) = Data.String.nil
  (StrSkip n (Data.String.cons x xs)) = (StrSkip (- n 1) xs)

  (StrTake 0 _) = Data.String.nil
  (StrTake n Data.String.nil) = Data.String.nil
  (StrTake n (Data.String.cons x xs)) = (Data.String.cons x (StrTake (- n 1) xs))

  (StrSubstr start len str) = (StrTake len (StrSkip start str))

  (Unpack (Data.String.cons x xs)) = (Prelude.Basics..colon.colon x (Unpack xs))
  (Unpack Data.String.nil) = Prelude.Basics.Nil

  (Force !x) = x

  Id = λx x

  """

showcCleanStringChar : Char -> String -> String
showcCleanStringChar ' ' = ("_" ++)
showcCleanStringChar '!' = (".bang" ++)
showcCleanStringChar '"' = (".quotation" ++)
showcCleanStringChar '#' = (".number" ++)
showcCleanStringChar '$' = (".dollar" ++)
showcCleanStringChar '%' = (".percent" ++)
showcCleanStringChar '&' = (".and" ++)
showcCleanStringChar '\'' = (".tick" ++)
showcCleanStringChar '(' = (".parenOpen" ++)
showcCleanStringChar ')' = (".parenClose" ++)
showcCleanStringChar '*' = (".star" ++)
showcCleanStringChar '+' = (".plus" ++)
showcCleanStringChar ',' = (".comma" ++)
showcCleanStringChar '-' = ("__" ++)
showcCleanStringChar '.' = (".dot" ++)
showcCleanStringChar '/' = (".slash" ++)
showcCleanStringChar ':' = (".colon" ++)
showcCleanStringChar ';' = (".semicolon" ++)
showcCleanStringChar '<' = (".lt" ++)
showcCleanStringChar '=' = (".eq" ++)
showcCleanStringChar '>' = (".gt" ++)
showcCleanStringChar '?' = (".question" ++)
showcCleanStringChar '@' = (".at" ++)
showcCleanStringChar '[' = (".bracketOpen" ++)
showcCleanStringChar '\\' = ("_backslash" ++)
showcCleanStringChar ']' = (".bracketClose" ++)
showcCleanStringChar '^' = (".hat" ++)
showcCleanStringChar '_' = ("." ++)
showcCleanStringChar '`' = (".backquote" ++)
showcCleanStringChar '{' = (".braceOpen" ++)
showcCleanStringChar '|' = (".or" ++)
showcCleanStringChar '}' = (".braceClose" ++)
showcCleanStringChar '~' = (".tilde" ++)
showcCleanStringChar c
   = if c < chr 32 || c > chr 126
        then (("u" ++ leftPad '0' 4 (asHex (cast c))) ++)
        else strCons c

showcCleanString : List Char -> String -> String
showcCleanString [] = id
showcCleanString (c ::cs) = (showcCleanStringChar c) . showcCleanString cs

cleanString : String -> String
cleanString cs = showcCleanString (unpack cs) ""

hvmUserName : UserName -> String
hvmUserName (Basic n) = cleanString n
hvmUserName (Field n) = "rec." ++ cleanString n
hvmUserName Underscore = cleanString "_"

headUpper : StrM str -> String
headUpper (StrCons x xs) = strCons (toUpper x) xs
headUpper StrNil = ""

hvmNameStr : Name -> String
hvmNameStr (NS ns n) = (showNSWithSep "." ns) ++ "." ++ hvmNameStr n
hvmNameStr (UN n) =
  let userName = hvmUserName n in
  if isPrefixOf "prim" userName 
    then headUpper $ strM userName
    else userName
hvmNameStr (MN n i) = cleanString n ++ "." ++ cleanString (show i)
hvmNameStr (PV n d) = "pat." ++ hvmNameStr n
hvmNameStr (DN _ n) = hvmNameStr n
hvmNameStr (Nested i n) = "n." ++ cleanString (show i) ++ "_" ++ hvmNameStr n
hvmNameStr (CaseBlock x y) = "case." ++ cleanString (show x) ++ "_" ++ cleanString (show y)
hvmNameStr (WithBlock x y) = "with." ++ cleanString (show x) ++ "_" ++ cleanString (show y)
hvmNameStr (Resolved i) = "fn." ++ cleanString (show i)

hvmName : Name -> Builder
hvmName = singleton . hvmNameStr

primString : List Char -> String
primString (x :: xs) = "(Data.String.cons " ++ (show $ ord x) ++ " " ++ primString xs ++ ")"
primString [] = "Data.String.nil"

primValStr : Constant -> String
primValStr (Str x) = primString $ unpack x
primValStr (Ch x) = show $ ord x
primValStr WorldVal = "Id"
primValStr val = show val

primVal : Constant -> Builder
primVal = singleton . primValStr

altByCon : Name -> List NamedConAlt -> (Maybe NamedConAlt, List NamedConAlt)
altByCon _ [] = (Nothing, [])
altByCon con (alt@(MkNConAlt c _ _ _ _) :: alts) =
  if con == c then
    (Just alt, alts)
  else
    let (retAlt, restAlts) = altByCon con alts in
    (retAlt, alt :: restAlts)

hvmPrimFn : PrimFn ar -> Vect ar Builder -> Builder
hvmPrimFn StrAppend [x, y] = "String.concat " ++ x ++ " " ++ y
hvmPrimFn StrCons [x, y] = "Data.String.cons " ++ x ++ " " ++ y
hvmPrimFn StrHead [x] = "StrHead " ++ x
hvmPrimFn StrTail [x] = "StrTail " ++ x
hvmPrimFn StrReverse [x] = "StrRev Data.String.nil " ++ x
hvmPrimFn StrLength [x] = "StrLen " ++ x
hvmPrimFn StrIndex [x, y] = "StrIdx " ++ x ++ " " ++ y
hvmPrimFn StrSubstr [x, y, z] = "StrSubstr " ++ x ++ " " ++ y ++ " " ++ z
hvmPrimFn BelieveMe [_, _, x] = x
hvmPrimFn (Cast IntType StringType) [x] = "ToString " ++ x
hvmPrimFn (Cast IntegerType StringType) [x] = "ToString " ++ x
hvmPrimFn (Cast IntType IntegerType) [x] = x
hvmPrimFn (Cast IntegerType IntType) [x] = x
hvmPrimFn (Cast IntType CharType) [x] = x
hvmPrimFn (Cast CharType IntType) [x] = x
hvmPrimFn (Cast CharType IntegerType) [x] = x
hvmPrimFn (Add ty) [x, y] = "+ " ++ x ++ " " ++ y
hvmPrimFn (Sub ty) [x, y] = "- " ++ x ++ " " ++ y
hvmPrimFn (Mul ty) [x, y] = "* " ++ x ++ " " ++ y
hvmPrimFn (Div ty) [x, y] = "/ " ++ x ++ " " ++ y
hvmPrimFn (Mod ty) [x, y] = "% " ++ x ++ " " ++ y
hvmPrimFn (BAnd ty) [x, y] = "& " ++ x ++ " " ++ y
hvmPrimFn (BOr ty) [x, y] = "| " ++ x ++ " " ++ y
hvmPrimFn (BXOr ty) [x, y] = "^ " ++ x ++ " " ++ y
hvmPrimFn (ShiftL ty) [x, y] = "<< " ++ x ++ " " ++ y
hvmPrimFn (ShiftR ty) [x, y] = ">> " ++ x ++ " " ++ y
hvmPrimFn (LT ty) [x, y] = "< " ++ x ++ " " ++ y
hvmPrimFn (LTE ty) [x, y] = "<= " ++ x ++ " " ++ y
hvmPrimFn (EQ ty) [x, y] = "== " ++ x ++ " " ++ y
hvmPrimFn (GTE ty) [x, y] = ">= " ++ x ++ " " ++ y
hvmPrimFn (GT ty) [x, y] = "> " ++ x ++ " " ++ y
hvmPrimFn fn _ = assert_total $ idris_crash $ "Prim function " ++ show fn ++ " not implemented"

hvmLam : List Name -> Builder
hvmLam [] = ""
hvmLam (n :: names) = "λ" ++ hvmName n ++ " " ++ hvmLam names

hvmArgs : Builder -> Nat -> Builder
hvmArgs _ Z = ""
hvmArgs arg (S n) = arg ++ (singleton $ show n) ++ " " ++ hvmArgs arg n

mutual
  hvmCase :  {auto defs : Ref Ctxt Defs}
          -> {auto cons : ConsInfo}
          -> {auto mdef : Maybe NamedCExp} 
          -> List (Nat, Name)
          -> List NamedConAlt 
          -> Core Builder
  hvmCase [] _ = pure ""
  hvmCase ((arity, con) :: rest) alts =
    case altByCon con alts of
      (Just (MkNConAlt _ ci tag args exp), restAlts) =>
        pure $ "(" ++ hvmLam args ++ !(hvmCExp exp) ++ ") " ++ !(hvmCase rest restAlts)
      (Nothing, restAlts) =>
        -- If there is no case for the given constructor, then use default 
        pure $ "(" ++ sepBy " " (replicate arity "λ_") ++ " " ++ !(maybe (pure "NotCoveredCase") hvmCExp mdef) ++ ") " ++ !(hvmCase rest restAlts) 

  hvmCExp :  {auto defs : Ref Ctxt Defs}
          -> {auto cons : ConsInfo}
          -> NamedCExp 
          -> Core Builder
  hvmCExp (NmLocal fc n) = pure $ hvmName n
  hvmCExp (NmRef fc n) = pure $ hvmName n
  hvmCExp (NmLam fc n rhs) = pure $ "λ" ++ hvmName n ++ " " ++ !(hvmCExp rhs)
  hvmCExp (NmLet fc n@(MN "act" _) (NmApp _ act args@(_ :: _)) cont) =
    -- convert all world arguments to continuation
    hvmCExp (NmApp fc act $ snoc (init args) (NmLam fc n cont))
  hvmCExp (NmLet fc n val rhs) = pure $ "let " ++ hvmName n ++ " = " ++ !(hvmCExp val) ++ ";" ++ !(hvmCExp rhs)
  hvmCExp (NmApp fc f args) = do
    let args = (sepBy " " !(traverse hvmCExp args))
    pure $ "(" ++ !(hvmCExp {defs} f) ++ " " ++  args ++ ")"
  hvmCExp (NmCon fc cn ci mbTag args) =
    let args = (sepBy " " !(traverse hvmCExp args)) in
    pure $ "(" ++ hvmName cn ++ " " ++ args ++ ")"
  hvmCExp (NmCrash fc msg) = coreFail (InternalError "Crash not implemented")
  hvmCExp (NmForce fc lr rhs) = pure $ "(Force " ++ !(hvmCExp rhs) ++ ")"
  hvmCExp (NmDelay fc lr rhs) = hvmCExp rhs -- hvm lazy by default
  hvmCExp (NmErased fc) = pure "Erased"
  hvmCExp (NmPrimVal fc x) = pure $ primVal x
  hvmCExp (NmOp fc op args) = do
    args <- traverseVect hvmCExp args
    pure $ "(" ++ hvmPrimFn op args ++ ")"
  hvmCExp (NmExtPrim fc n args) = coreFail (InternalError "External primitive operations not implemented")
  hvmCExp (NmConCase fc sc alts mdef) = do
    let sctym = do
      (MkNConAlt con _ _ _ _) <- head' alts
      fst <$> find (\(_, _, c) => con == c) cons
    case sctym of
      Just scty => 
        let consScTy = filter (\(ty, _, _) => scty == ty) cons in
        pure $ 
          "(" ++ (hvmName scty ++ "match ") 
          ++ !(hvmCExp {cons} sc) ++ " " 
          ++ !(hvmCase {cons} (snd <$> consScTy) alts) ++ ")"
      Nothing => maybe (pure "") hvmCExp mdef
  hvmCExp (NmConstCase fc sc alts mdef) =
    pure $ "(Cond " ++ !(hvmCExp sc) ++ " [" ++ !(hvmConstAlt mdef alts) ++ "])"
    where
      hvmConstAlt : Maybe NamedCExp -> List NamedConstAlt -> Core Builder
      hvmConstAlt Nothing [MkNConstAlt c rhs] = pure $ "(Default " ++ !(hvmCExp rhs) ++ ")"
      hvmConstAlt mdef (MkNConstAlt c rhs :: alts) =
        pure $ "(Case " ++ primVal c ++ " " ++ !(hvmCExp rhs) ++ "), " ++ !(hvmConstAlt mdef alts)
      hvmConstAlt (Just def) [] = pure $ "(Default " ++ !(hvmCExp def) ++ ")"
      hvmConstAlt Nothing [] = pure ""

hvmDef :  {auto defs : Ref Ctxt Defs}  
       -> {auto cons : ConsInfo}
       -> Name
       -> NamedDef
       -> Core Builder
hvmDef name (MkNmFun args expr) = do
  pure $ "(" ++ !(hvmName <$> toFullNames name) ++ " " ++
  sepBy " " (hvmName <$> args) ++ ") = " ++ !(hvmCExp expr) ++ "\n"
hvmDef name (MkNmCon tag arity nt) = pure "" -- no need https://github.com/HigherOrderCO/HVM/tree/master/guide#constructors
hvmDef name (MkNmForeign ccs argTys retTy) = case name of
  NS _ (UN (Basic "prim__putStr")) =>
    pure $ "(" ++ !(hvmName <$> toFullNames name) ++ " str cont) = (Apps.HVM.print str (cont Builtin.MkUnit))\n"
  NS _ (UN (Basic "prim__getStr")) =>
    pure $ "(" ++ !(hvmName <$> toFullNames name) ++ " cont) = (Apps.HVM.query cont)\n"
  NS _ (UN (Basic "fastUnpack")) =>
    pure $ "(" ++ !(hvmName <$> toFullNames name) ++ " str) = (Unpack str)\n"
  _ => coreFail $ (InternalError $ "Foreign function " ++ show !(toFullNames name) ++ "not implemented")
hvmDef name (MkNmError msg) = pure ""

retType : {vars : _} -> Term vars -> (vars' ** Term vars')
retType (Bind _ _ _ f) = retType f
retType (App _ f a) = retType f
retType t = (vars ** t)

||| By the name of the constructor, we get its type and arity
conTypeAndArity :  {auto defs : Ref Ctxt Defs} 
                -> Name 
                -> NamedDef 
                -> Core (Maybe (Name, Nat, Name))
conTypeAndArity name (MkNmCon tag arity nt) = do
  defs <- get Ctxt
  Just def <- lookupCtxtExact name (gamma defs)
    | _ => pure Nothing
  let (_ ** retTy) = retType def.type
  case retTy of
      Ref _ _ nameTy => pure $ Just (!(toFullNames nameTy), arity, !(toFullNames name))
      _ => pure Nothing
conTypeAndArity {} = pure Nothing

||| Creating a matching rule that takes scrutinee as the first argument, 
||| followed by a continuation function for different cases
hvmMatchFunction : Builder -> Nat -> List (Nat, Name) -> Builder
hvmMatchFunction name covered ((arity, con) :: rest) =
  let args = hvmArgs "arg" arity in
  "(" ++ name ++ " (" ++ hvmName con ++ " " ++ args ++ ") " 
  ++ sepBy " " (replicate covered "_") ++ " f " ++ sepBy " " (replicate (length rest) "_") ++ ")" ++
  " = (" ++ "f " ++ args ++ ")\n" ++ hvmMatchFunction name (S covered) rest
hvmMatchFunction _ _ [] = ""

hvmMatches : ConsInfo -> Builder
hvmMatches conMap@((nameTy, arity, con) :: _) =
  let (conMap, rest) = partition (\(ty, _, _) => nameTy == ty) conMap in
  hvmMatchFunction (hvmName nameTy ++ "match") Z ((\(_, arc) => arc) <$> conMap) ++ hvmMatches rest
hvmMatches [] = ""

compile :
  Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (execDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile defs syn tmp dir term file = do
    compData <- getCompileData False Cases term
    let ndefs = namedDefs compData
    conInfo <- catMaybes <$> traverse (\(n, (_, def)) => conTypeAndArity n def) ndefs
    hvmCode <- concat <$> traverse (\(n, (_, def)) => hvmDef n def) ndefs
    let outn = dir </> file ++ ".hvm"
    writeFile outn $ build 
      $ predefined 
      ++ hvmMatches conInfo 
      ++ hvmCode
      ++ "\nMain = " ++ !(hvmCExp $ forget compData.mainExpr)
    pure $ Just outn

execute :
  Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
  (execDir : String) -> ClosedTerm -> Core ()
execute defs syn dir term = do
    outn <- compile defs syn dir dir term "_tmp_hvm"
    case outn of
        Just outn => map (const ()) $ coreLift $ system $ "hvm run -f " ++ outn
        Nothing => pure ()

hvmCodegen : Codegen
hvmCodegen = MkCG compile execute Nothing Nothing

main : IO ()
main = mainWithCodegens [("hvm", hvmCodegen)]
