module Utils where

import Absgrammar 
import qualified Data.Map as Map
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.List (genericReplicate)
import Data.Maybe

data EnvVal = FunVal Declaration Env Integer | Loc Integer deriving (Eq, Ord, Show)
type Env = Map.Map Ident EnvVal

data Value = BoolVal Bool | IntVal Integer | ArrayValue [Value] deriving (Eq, Ord)
type Store = (Map.Map Integer Value, Integer)

instance Show Value where
	show (BoolVal b) = show b
	show (IntVal i) = show i

type Eval a = ReaderT Env (ErrorT String (StateT Store IO)) a

------------------- Utils -----------------------------------------------------

emptyEnv :: Env
emptyEnv = Map.empty

emptyStore :: Store
emptyStore = (Map.empty, 0)

defaultValue :: Type -> Value 
defaultValue (SType TInt) = (IntVal 0)
defaultValue (SType TBool) = (BoolVal True)
defaultValue (AType size TInt) = (ArrayValue (genericReplicate size (IntVal 0)))
defaultValue (AType size TBool) = (ArrayValue (genericReplicate size (BoolVal True)))

getFromArray :: Integer -> [Value] -> Eval Value
getFromArray i xs =
	let n = fromIntegral (i :: Integer) in
		if (n < 0) || (n >= (length xs)) then
			throwError $ "ERROR: Array index out of bounds"
		else
			return (xs !! n)

insertToArray :: Integer -> [Value] -> Value -> Eval [Value]
insertToArray i xs val =
	let n = fromIntegral (i :: Integer) in
		if (n < 0) || (n >= (length xs)) then
			throwError $ "ERROR: Array index out of bounds"
		else	
			return ((take n xs) ++ [val] ++ (drop (n+1) xs))

getVar :: Ident -> Eval Value
getVar id =
	do
		env <- ask
		(st, _) <- get
		case (env Map.! id) of
			(Loc loc) -> return (st Map.! loc)
			(FunVal _ _ loc) -> return (st Map.! loc)

getValue :: Variable -> Eval Value
getValue (Var id) = getVar id
getValue (ArrayVar id exp) =
	do 
		(ArrayValue l) <- getVar id
		(IntVal n) <- evalExp exp
		getFromArray n l

setVar :: Ident -> Value -> Eval ()
setVar id val =
	do
		env <- ask
		(st, new_loc) <- get
		case (env Map.! id) of
			(Loc loc) -> modify (const ((Map.insert loc val st), new_loc))
			(FunVal _ _ loc) -> modify (const ((Map.insert loc val st), new_loc))

setValue :: Variable -> Value -> Eval ()
setValue (Var id) val = setVar id val
setValue (ArrayVar id exp) val =
	do
		(ArrayValue l) <- getVar id
		(IntVal n) <- evalExp exp
		new_array <- insertToArray n l val
		setVar id (ArrayValue new_array)

------------------- Declarations ----------------------------------------------
evalDecls :: [Declaration] -> Eval Env
evalDecls [] = ask
evalDecls ((VarDec id t):xs) =
	do
		(st, loc) <- get
		modify (const (Map.insert loc (defaultValue t) st, loc+1))
		local (Map.insert id (Loc loc)) (evalDecls xs)
evalDecls (f@(FunDec (FunHead id args t) decls stmts):xs) =
	do
		(st, loc) <- get
		modify (const (st, loc+1))
		env <- ask
		local (Map.insert id (FunVal f env loc)) (evalDecls xs)
evalCallArgs :: [Argument] -> [CallArgument] -> Env -> Eval Env
evalCallArgs [] [] fun_env = return fun_env
evalCallArgs ((ValArg id _):xs) ((ExpArg exp):ys) fun_env =
	do
		val <- evalExp exp
		(st, loc) <- get
		modify (const (Map.insert loc val st, loc+1))
		(evalCallArgs xs ys (Map.insert id (Loc loc) fun_env))
evalCallArgs ((RefArg id _):xs) ((ExpArg (EVar (Var cid))):ys) fun_env =
	do
		env <- ask
		let (Loc l) = (env Map.! cid) in
			(evalCallArgs xs ys (Map.insert id (Loc l) fun_env))
 
evalCallArgs ((FunArg (FunHead id args t)):xs) ((AnonFun (AnonFunHead _ _) exp):ys) fun_env =
	do
		env <- ask
		(st, loc) <- get
		modify (const (st,loc+1))
		let fun = (FunDec (FunHead id args t) (DecBlock []) (StmBlock [(SAssign (Var id) exp)])) in
			(evalCallArgs xs ys (Map.insert id (FunVal fun env loc) fun_env))

evalCallArgs ((FunArg (FunHead id _ _)):xs) ((ExpArg (EVar (Var cid))):ys) fun_env =
	do
		env <- ask
		let fun  = env Map.! cid in
			(evalCallArgs xs ys (Map.insert id fun fun_env))

showMap :: Env -> String
showMap env = foldl (\s (Ident id, _) ->(s ++ " " ++ id )) "" (Map.toList env)

------------------- Statements ------------------------------------------------
evalStmts :: [Statement] -> Eval ()
evalStmts xs = forM_ xs evalStmt

evalAssignStmt :: Variable -> Exp -> (Integer -> Integer -> Integer) -> Eval ()
evalAssignStmt var exp f =
	do
		(IntVal a) <- getValue var
		(IntVal b) <- evalExp exp
		setValue var (IntVal (f a b))

evalStmt :: Statement -> Eval ()
evalStmt (SBlock stmts) = evalStmts stmts
evalStmt (SWhile exp stmt) =
	do
		(BoolVal b) <- evalExp exp
		when b (evalStmt stmt >> evalStmt (SWhile exp stmt))
evalStmt (SDoWhile stmt exp) =
	do
		evalStmt stmt
		evalStmt (SWhile exp stmt)
evalStmt (SFor id exp1 exp2 stmt) =
	do
		(IntVal a) <- evalExp exp1
		(IntVal b) <- evalExp exp2
		let n = fromIntegral ((b-a+1) :: Integer) in
			when (a <= b) $ setValue (Var id) (IntVal a) >> replicateM_ n (evalStmt stmt >> evalExp (EInc (Var id)))
evalStmt (SAssign var exp) =
	do
		val <- evalExp exp
		setValue var val
evalStmt (SPlusA var exp) = evalAssignStmt var exp (+)
evalStmt (SMinusA var exp) = evalAssignStmt var exp (-)
evalStmt (SMulA var exp) = evalAssignStmt var exp (*)
evalStmt (SDivA var exp) =
		do
			(IntVal a) <- getValue var
			(IntVal b) <- evalExp exp
			when (b==0) (return () >> throwError "ERROR: Division by zero")
			setValue var (IntVal (a `div` b))
evalStmt (SPrint exp) = evalExp exp >>= liftIO . putStr . (++" ") . show
evalStmt (SPrintln) = liftIO $ putStrLn ""
evalStmt (SIf exp stmt) =
	do
		(BoolVal b) <- evalExp exp
		when b (evalStmt stmt)
evalStmt (SIfElse exp stmt1 stmt2) =
	do 
		(BoolVal b) <- evalExp exp
		if b then
			evalStmt stmt1
		else
			evalStmt stmt2
evalStmt (SExp exp) = evalExp exp >> return ()
evalStmt (SFunCall id cargs) = evalExp (EFunCall id cargs) >> return ()
------------------- Expressions -----------------------------------------------			
evalIntBoolExp :: Exp -> Exp -> (Integer -> Integer -> Bool) -> Eval Value
evalIntBoolExp exp1 exp2 f =
	do
		(IntVal a) <- evalExp exp1
		(IntVal b) <- evalExp exp2
		return (BoolVal (f a b))

evalIntIntExp :: Exp -> Exp -> (Integer -> Integer -> Integer) -> Eval Value
evalIntIntExp exp1 exp2 f =
	do 
		(IntVal a) <- evalExp exp1
		(IntVal b) <- evalExp exp2
		return (IntVal (f a b))

evalBoolBoolExp :: Exp -> Exp -> (Bool -> Bool -> Bool) -> Eval Value
evalBoolBoolExp exp1 exp2 f = 
	do 
		(BoolVal a) <- evalExp exp1
		(BoolVal b) <- evalExp exp2
		return (BoolVal (f a b))
evalEqualExp :: Exp -> Exp -> (Value -> Value -> Bool) -> Eval Value
evalEqualExp exp1 exp2 f =
	do
		a <- evalExp exp1 
		b <- evalExp exp2
		return (BoolVal (f a b))  

evalExp :: Exp -> Eval (Value)
evalExp (EConst (IConst x)) = return (IntVal x)
evalExp (EConst BTrue) = return (BoolVal True)
evalExp (EConst BFalse) = return (BoolVal False)
evalExp (EVar var) = getValue var
evalExp (EGe exp1 exp2) = evalIntBoolExp exp1 exp2 (>)
evalExp (EGeq exp1 exp2) = evalIntBoolExp exp1 exp2 (>=)
evalExp (ELe exp1 exp2) = evalIntBoolExp exp1 exp2 (<)
evalExp (ELeq exp1 exp2) = evalIntBoolExp exp1 exp2 (<=)
evalExp (EEq exp1 exp2) = evalEqualExp exp1 exp2 (==)
evalExp (ENotEq exp1 exp2) = evalEqualExp exp1 exp2 (/=)
evalExp (EPlus exp1 exp2) = evalIntIntExp exp1 exp2 (+)
evalExp (EMinus exp1 exp2) = evalIntIntExp exp1 exp2 (-)
evalExp (EMul exp1 exp2) = evalIntIntExp exp1 exp2 (*)
evalExp (EPow exp1 exp2) = evalIntIntExp exp1 exp2 (^)
evalExp (EDiv exp1 exp2) =
	do 
		(IntVal a) <- evalExp exp1
		(IntVal b) <- evalExp exp2
		when (b==0) (return () >> throwError "ERROR: Division by zero")
		return (IntVal (a `div` b))
evalExp (EOr exp1 exp2) = evalBoolBoolExp exp1 exp2 (||)
evalExp (EAnd exp1 exp2) = evalBoolBoolExp exp1 exp2 (&&)
evalExp (ENot exp) =
	do
		(BoolVal a) <- evalExp exp
		return (BoolVal (not a))
evalExp (ENeg exp) =
	do
		(IntVal a) <- evalExp exp
		return (IntVal (-a))
evalExp (EInc var) =
	do
		(IntVal a) <- getValue var
		setValue var (IntVal (a+1))
		return (IntVal a)
evalExp (EDec var) =
	do
		(IntVal a) <- getValue var
		setValue var (IntVal (a-1))
		return (IntVal a)
evalExp (EFunCall id (CallArgs cargs)) =
	do
		map <- ask
		let f@(FunVal (FunDec (FunHead _ (Args args) t) (DecBlock decls) (StmBlock stmts)) fenv fun_loc) = (map Map.! id) in
			do
				fun_env <- (evalCallArgs args cargs fenv)
				(st, loc) <- get
				modify (const (Map.insert fun_loc (defaultValue (SType t)) st, loc))
				local (const (Map.insert id f fun_env)) (do {
					env2 <- evalDecls decls; 
					local (const env2) (evalStmts stmts);
				})
				(st, _) <- get
				return (st Map.! fun_loc)
------------------- Program ---------------------------------------------------

evalProgram :: Program -> Eval ()
evalProgram (Prog (DecBlock decls) (StmBlock stmts)) =
	do
		env <- evalDecls decls
		local (const env) (evalStmts stmts)

runEvalProgram :: Program -> IO (Either String (), Store)
runEvalProgram prog = runStateT (runErrorT (runReaderT (evalProgram prog) emptyEnv)) emptyStore
