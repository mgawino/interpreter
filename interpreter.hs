module Main where

import System.Environment (getArgs)

import Lexgrammar
import Pargrammar
import Skelgrammar
import Printgrammar
import Absgrammar
import Utils (runEvalProgram)
import Static (runStaticAnalysis)
import Data.Map (toList)
import System.IO (hPutStrLn, stderr)
  
import ErrM

main :: IO ()
main = do
	args <- getArgs
	if length args == 0 then
		error "File not specified"
	else
		do
			s <- readFile (args !! 0)
			case pProgram (myLexer s) of
				Ok p ->
					do
						(res,_) <- (runStaticAnalysis p)
						case res of
							(Left err) -> hPutStrLn stderr err
							(Right _) -> do
											(res, _) <- (runEvalProgram p)
											case res of 
												(Left err) -> hPutStrLn stderr err
												(Right msg) -> putStrLn "OK"
				Bad e -> hPutStrLn stderr e
