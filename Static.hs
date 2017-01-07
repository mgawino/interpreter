{-# LANGUAGE ExistentialQuantification #-}

module Static where

import Absgrammar
import Printgrammar
import qualified Data.Map as Map
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.State
import Data.Maybe

type EnvMap = Map.Map Ident Value
type Env = (EnvMap, Printable, Ident)
data Printable = forall a. Print a => PPrint a

instance Show Printable where
    show (PPrint a) = printTree a

newtype ShowType = ST GenType

showId :: Ident -> String
showId (Ident id) = id

showType :: GenType -> String
showType (GAType t) = "array of " ++ showType (GSType t)
showType (GSType TInt) = "int"
showType (GSType TBool) = "bool"

data Value = VDec GenType | FDec [Argument] GenType deriving (Eq, Show)

type Eval a = ReaderT Env (ErrorT String IO) a

-- Utils
insertEnv :: EnvMap -> (EnvMap -> EnvMap) -> Printable -> Ident -> Eval () 
emptyEnv = 
emptyEnv = (Map.empty, Ident "", Ident "")

convertType :: Type -> GenType
convertType (SType t) = GSType t
convertType (AType _ t) = GAType t

convertSimpleType :: SimpleType -> GenType
convertSimpleType t = GSType t

getContext :: Eval String
getContext = get >>= \(p,_) -> return (" \n\tin " ++ show p)

checkExists :: Env -> Ident -> Eval ()
checkExists (env, _, _) id =
    case Map.lookup id env of
        (Just _) -> throwError $ "ERROR: Duplicate identifier: " ++ showId id
        (Nothing) -> return ()

checkTypes :: GenType -> GenType -> Eval ()
checkTypes t1 t2 =
    do
        c <- getContext
        when (t1 /= t2)
            (return () >> throwError $ "Error: Incompatibile types: got " ++ 
                          (showType t2) ++ " expected " ++ (showType t1) ++ c)
 
checkVarType :: Variable -> SimpleType -> Eval ()
checkVarType var t = getVarType var >>= \vt -> checkTypes (convertSimpleType t) (convertSimpleType vt)

getVarType :: Variable -> Eval SimpleType
getVarType (Var id) =
    do
        (env, _, _) <- ask
        c <- getContext
        case Map.lookup id env of
            Just (VDec (GAType _)) -> throwError $ "Error: Missing qualifier with \"" ++ 
                                                    (showId id) ++ "\"" ++ c
            Just (VDec (GSType t)) -> return t
            Just (FDec _ (GSType t)) ->
                do
                    (p, fun) <- get 
                    if id == fun then
                        return t
                    else    
                        throwError $ "Error: Can't read or write a function type" ++ c
            Nothing -> throwError $ "Error: Identifier not found \"" ++ (showId id) ++ "\"" ++ c
getVarType (ArrayVar id exp) =
    do
        (env, _, _) <- ask
        c <- getContext
        case Map.lookup id env of
            Just (VDec (GAType t)) -> evalExpTypes [(exp, TInt)] >> return t
            Nothing -> throwError $ "Error: Identifier not found \"" ++ (showId id) ++ "\"" ++ c
            Just (VDec t) -> throwError $ "Error: Illegal qualifier with \"" ++ showId id ++ "\"" ++ c
-- Declarations

checkDecls :: [Declaration] -> Env -> Eval Env
checkDecls [] env = ask
checkDecls ((VarDec id t):xs) e@(check_env, a, b) =
    let env = (Map.insert id (VDec (convertType t)) check_env, a, b) in
        checkExists e id >> local (Map.insert id (VDec (convertType t))) (checkDecls xs env)
checkDecls ((FunDec (FunHead id (Args args) t) (DecBlock decls) (StmBlock stmts)):xs) check_env =
    do
        loc_env <- ask
        checkExists check_env id
        let fun_env = (Map.insert id (FDec args (convertSimpleType t)) emptyEnv) in
            do
                args_env <- (checkArgs fun_env args)
                dec_env <- local (const (Map.union args_env loc_env)) (checkDecls decls args_env)
                local (const (Map.union dec_env args_env)) (put (PPrint "",id) >> checkStmts stmts >> put emptyStore)
                let env = (Map.union fun_env loc_env)
                local (const env) (checkDecls xs env)

checkArgs :: Env -> [Argument] -> Eval Env
checkArgs env args = foldM checkArg env args
checkArg :: Env -> Argument -> Eval Env
checkArg env (ValArg id t) = checkExists env id >> return (Map.insert id (VDec t) env)
checkArg env (RefArg id t) = checkExists env id >> return (Map.insert id (VDec t) env)
checkArg env (FunArg (FunHead id (Args args) t)) = 
    checkExists env id >> checkUniqueArgs args >> return (Map.insert id (FDec args (convertSimpleType t)) env)

checkUniqueArgs :: [Argument] -> Eval ()
checkUniqueArgs args = foldM checkUniqueArg emptyEnv args >> return ()
checkUniqueArg :: Env -> Argument -> Eval Env
checkUniqueArg env (ValArg id t) = checkExists env id >> return (Map.insert id (VDec t) env)
checkUniqueArg env (RefArg id t) = checkExists env id >> return (Map.insert id (VDec t) env)
checkUniqueArg env (FunArg (FunHead id (Args args) t)) = 
    checkExists env id >> checkUniqueArgs args >> return (Map.insert id (VDec (convertSimpleType t)) env)

checkFunArgs :: [Argument] -> [Argument] -> Eval ()
checkFunArgs args1 args2 =
    do
        c <- getContext
        if (length args1) /= (length args2) then
            throwError $ "Error: Wrong number of parameters specified for function call" ++ c
        else
            zipWithM_ checkFunArg args1 args2
checkFunArg :: Argument -> Argument -> Eval ()
checkFunArg (ValArg _ t1) (ValArg _ t2) = checkTypes t1 t2
checkFunArg (RefArg _ t1) (RefArg _ t2) = checkTypes t1 t2
checkFunArg (FunArg (FunHead _ (Args args1) t1)) (FunArg (FunHead _ (Args args2) t2)) = 
    checkTypes (convertSimpleType t1) (convertSimpleType t2) >> checkFunArgs args1 args2
checkFunArg _ _ = 
    do
        c <- getContext
        throwError $ "Error: Invalid argument passed to function" ++ c

checkFunCall :: [Argument] -> [CallArgument] -> Ident -> Eval ()
checkFunCall args cargs id =
    do
        c <- getContext
        if (length args) /= (length cargs) then
            throwError $ "Error: Wrong number of parameters specified for function call" ++ c
        else
            zipWithM_ checkCallArg args cargs
checkCallArg :: Argument -> CallArgument -> Eval ()
checkCallArg (ValArg _ t) (ExpArg (EVar (Var id))) =
    do
        env <- ask
        c <- getContext
        case Map.lookup id env of
            Just (VDec vt) -> checkTypes vt t
            Nothing -> throwError $ "Error: Identifier not found \"" ++ (showId id) ++ "\"" ++ c
            otherwise -> throwError $ "Error: Invalid argument passed to function \"" ++ (showId id) ++ "\"" ++ c
checkCallArg (ValArg _ t) (ExpArg exp) = evalExpType exp >>= \et -> checkTypes t (convertSimpleType et)
checkCallArg (RefArg _ t) (ExpArg (EVar (Var id))) =
    do
        env <- ask
        c <- getContext
        case Map.lookup id env of
            Just (VDec vt) -> checkTypes vt t
            Nothing -> throwError $ "Error: Identifier not found \"" ++ (showId id) ++ "\"" ++ c
            otherwise -> throwError $ "Error: Invalid argument passed to function \"" ++ (showId id) ++ "\"" ++ c
checkCallArg (FunArg (FunHead id (Args args1) t1)) (AnonFun (AnonFunHead (Args args2) t2) exp) =
    do
        checkTypes (convertSimpleType t1) (convertSimpleType t2) >> checkFunArgs args1 args2
        let fun = (FunDec (FunHead id (Args args2) t2) (DecBlock []) (StmBlock [(SAssign (Var id) exp)])) in
            checkDecls [fun] emptyEnv >> return ()
checkCallArg (FunArg (FunHead id (Args args1) t)) (ExpArg (EVar (Var cid))) =
    do
        env <- ask
        c <- getContext
        case Map.lookup cid env of
            Just (FDec args2 ft) -> checkTypes ft (convertSimpleType t) >> checkFunArgs args1 args2  
            Nothing -> throwError $ "Error: Identifier not found \"" ++ (showId id) ++ "\"" ++ c
            otherwise -> throwError $ "Error: Invalid argument passed to function" ++ c
checkCallArg _ _ = 
    do  
        c <- getContext
        throwError $ "Error: Invalid argument passed to function" ++ c
-- Statements
_checkStmt :: Statement -> Eval ()
_checkStmt s@(SBlock stmts) = checkStmt s
_checkStmt stmt = get >>= \(p, fun) -> put ((PPrint stmt), fun) >> checkStmt stmt

checkStmts :: [Statement] -> Eval ()
checkStmts stmts = forM_ stmts _checkStmt

checkAssignStmt :: Variable -> Exp -> Eval ()
checkAssignStmt var exp =
    do
        t1 <- getVarType var
        t2 <- evalExpType exp
        checkTypes (convertSimpleType t1) (convertSimpleType t2)

checkStmt :: Statement -> Eval ()
checkStmt (SBlock stmts) = checkStmts stmts
checkStmt (SWhile exp stmt) = _evalExpTypes [(exp, TBool)] >> _checkStmt stmt
checkStmt (SDoWhile stmt exp) = _evalExpTypes [(exp, TBool)] >> _checkStmt stmt
checkStmt (SFor id exp1 exp2 stmt) = checkVarType (Var id) TInt >> _evalExpTypes [(exp1, TInt), (exp2, TInt)] >> _checkStmt stmt
checkStmt (SAssign var exp) = checkAssignStmt var exp
checkStmt (SPlusA var exp) = checkAssignStmt var exp
checkStmt (SMinusA var exp) = checkAssignStmt var exp
checkStmt (SMulA var exp) = checkAssignStmt var exp
checkStmt (SDivA var exp) = checkAssignStmt var exp
checkStmt (SPrint exp) = evalExpType exp >> return ()
checkStmt (SPrintln) = return ()
checkStmt (SIf exp stmt) = _evalExpTypes [(exp, TBool)] >> _checkStmt stmt
checkStmt (SIfElse exp stmt1 stmt2) = _evalExpTypes [(exp, TBool)] >> checkStmts [stmt1,stmt2]
checkStmt (SExp exp) = evalExpType exp >> return ()
checkStmt (SFunCall id cargs) = evalExpType (EFunCall id cargs) >> return ()
-- Expressions
_evalExpTypes :: [(Exp, SimpleType)] -> Eval ()
_evalExpTypes xs = mapM_ (\a@(exp, t) -> get >>= \(p,fun) -> put ((PPrint exp),fun) >> evalExpTypeT a) xs

evalExpTypes :: [(Exp, SimpleType)] -> Eval ()
evalExpTypes xs = mapM_ evalExpTypeT xs
evalExpTypeT :: (Exp, SimpleType) -> Eval ()
evalExpTypeT (exp, t) =
    do
        et <- evalExpType exp
        checkTypes (convertSimpleType t) (convertSimpleType et)

evalEqualExpType :: Exp -> Exp -> Eval SimpleType
evalEqualExpType exp1 exp2 =
    do
        t1 <- evalExpType exp1
        t2 <- evalExpType exp2
        checkTypes (convertSimpleType t1)  (convertSimpleType t2)
        return TBool
evalExpType :: Exp -> Eval SimpleType
evalExpType (EConst (IConst _)) = return TInt
evalExpType (EConst _) = return TBool
evalExpType (EVar var) = getVarType var
evalExpType (EGe exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TBool
evalExpType (EGeq exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TBool
evalExpType (ELe exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TBool
evalExpType (ELeq exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TBool
evalExpType (EEq exp1 exp2) = evalEqualExpType exp1 exp2
evalExpType (ENotEq exp1 exp2) = evalEqualExpType exp1 exp2
evalExpType (EPlus exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TInt
evalExpType (EMinus exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TInt
evalExpType (EMul exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TInt
evalExpType (EPow exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TInt
evalExpType (EDiv exp1 exp2) = evalExpTypes [(exp1, TInt),(exp2, TInt)] >> return TInt
evalExpType (EOr exp1 exp2) = evalExpTypes [(exp1, TBool),(exp2, TBool)] >> return TBool
evalExpType (EAnd exp1 exp2) = evalExpTypes [(exp1, TBool),(exp2, TBool)] >> return TBool
evalExpType (ENot exp) = evalExpTypes [(exp, TBool)] >> return TBool
evalExpType (ENeg exp) = evalExpTypes [(exp, TInt)] >> return TInt
evalExpType (EInc var) = checkVarType var TInt >> return TInt
evalExpType (EDec var) = checkVarType var TInt >> return TInt
evalExpType (EFunCall id (CallArgs cargs)) =
    do
        env <- ask
        c <- getContext
        case Map.lookup id env of
            Just (FDec args (GSType t)) -> checkFunCall args cargs id >> return t
            Nothing -> throwError $ "Error: Identifier not found \"" ++ (showId id) ++ "\"" ++ c
            otherwise -> throwError $ "Error: \"" ++ (showId id) ++ "\" is not a function" ++ c
-- Program
checkProgram :: Program -> Eval ()
checkProgram (Prog (DecBlock decls) (StmBlock stmts)) =
    do
        env <- checkDecls decls emptyEnv
        local (const env) (checkStmts stmts)

runStaticAnalysis :: Program -> IO (Either String ())
runStaticAnalysis prog = runErrorT (runReaderT (checkProgram prog) emptyEnv
