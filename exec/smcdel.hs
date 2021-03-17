module Main where

import Control.Arrow (second)
import Control.Monad (when,unless)
import Data.List (intercalate)
import Data.Version (showVersion)
import Paths_smcdel (version)
import System.Console.ANSI
import System.Directory (getTemporaryDirectory)
import System.Environment (getArgs,getProgName)
import System.Exit (exitFailure)
import System.Process (system)
import System.FilePath.Posix (takeBaseName)
import System.IO (Handle,hClose,hPutStrLn,stderr,stdout,openTempFile, hPutStr)
import SMCDEL.Internal.Lex
import SMCDEL.Internal.Parse
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Internal.MyHaskCUDD (createZddFromBdd)
--import qualified SMCDEL.Symbolic.S5
import SMCDEL.Symbolic.S5_CUDD
--import SMCDEL.Symbolic.S5_CUDD

main :: IO ()
main = do
  (input,options) <- getInputAndSettings
  let showMode = "-show" `elem` options
  let texMode = "-tex" `elem` options || showMode
  tmpdir <- getTemporaryDirectory
  (texFilePath,texFileHandle) <- openTempFile tmpdir "smcdel.tex"
  let outHandle = if showMode then texFileHandle else stdout
  unless texMode $ putStrLn infoline
  when texMode $ hPutStrLn outHandle texPrelude
  case parse $ alexScanTokens input of
    Left (lin,col) -> error ("Parse error in line " ++ show lin ++ ", column " ++ show col)
    Right (CheckInput vocabInts lawform obs jobs) -> do
      
      let mykns = KnS (map P vocabInts) (boolBddOf $! lawform) (map (second (map P)) obs)
      
      initZddVars vocabInts
      let myknsZ = KnSZ (map P vocabInts) (boolZddOf (map P vocabInts) $! lawform) (map (second (map P)) obs)
      let myknsZs0 = KnSZs0 (map P vocabInts) (boolZdds0Of (map P vocabInts) $! lawform) (map (second (map P)) obs)
      --let myconv = KnSZ (map P vocabInts) ( createZddFromBdd (boolBddOf $! lawform)) (map (second (map P)) obs)
      let myknsZf0 = KnSZf0 (map P vocabInts) (boolZddf0Of (map P vocabInts) $! lawform) (map (second (map P)) obs)
      let myknsZf0s0 = KnSZf0s0 (map P vocabInts) (boolZddf0s0Of (map P vocabInts) $! lawform) (map (second (map P)) obs)
      
      --hPutStrLn outHandle giveDebugTex
      if texMode then 
        hPutStrLn outHandle $ "The law: " ++ tex lawform  ++ " \\\\" 
        else hPutStrLn outHandle $ "The law: " ++ ppForm lawform  ++ " \\\\"


      when texMode $
        hPutStrLn outHandle $ unlines
          [ "\\section{Given Knowledge Structure}",
          --"knowledge structure with Bdd:\\", "\\[ (\\mathcal{F},s) = (" ++ tex ((mykns,[])::KnowScene) ++ ") \\]",
          "knowledge structure with Zdd:\\","\\[ (\\mathcal{F},s) = (" ++ tex ((myknsZ,[])::KnowScene) ++ ") \\]", 
          --"knowledge structure coversion to Zdd:\\","\\[ (\\mathcal{F},s) = (" ++ tex ((myconv,[])::KnowScene) ++ ") \\]",
          --"knowledge structure with Zdds0:\\","\\[ (\\mathcal{F},s) = (" ++ tex ((myknsZs0,[])::KnowScene) ++ ") \\]", 
          --"knowledge structure with Zddf0:\\","\\[ (\\mathcal{F},s) = (" ++ tex ((myknsZf0,[])::KnowScene) ++ ") \\]", 
          --"knowledge structure with Zddf0s0:\\","\\[ (\\mathcal{F},s) = (" ++ tex ((myknsZf0s0,[])::KnowScene) ++ ") \\]", 
          "\\section{Results}" ]
      mapM_ (doJob outHandle texMode mykns myknsZ myknsZs0 myknsZf0 myknsZf0s0) jobs

      when texMode $ hPutStrLn outHandle texEnd
      when showMode $ do
        hClose outHandle
        let command = "cd /tmp && pdflatex -interaction=nonstopmode " ++ takeBaseName texFilePath ++ ".tex > " ++ takeBaseName texFilePath ++ ".pdflatex.log && xdg-open "++ takeBaseName texFilePath ++ ".pdf"
        putStrLn $ "Now running: " ++ command
        _ <- system command
        return ()
      putStrLn "\nDoei!"

doJob :: Handle -> Bool -> KnowStruct -> KnowStruct -> KnowStruct -> KnowStruct -> KnowStruct -> Job -> IO ()
doJob outHandle True mykns myknsZ myknsZs0 myknsZf0 myknsZf0s0 (ValidQ f) = do
  hPutStrLn outHandle $ "Is $" ++ texForm (simplify f) ++ "$ valid on $\\mathcal{F}$?\n"
  hPutStrLn outHandle ("Bdd says: " ++ show (validViaDd mykns f) ++ "\n")
  hPutStrLn outHandle ("Zdd says: " ++ show (validViaDd myknsZ f) ++ "\n")
  hPutStrLn outHandle ("f in bdd form: " ++ texDdB (bddOf mykns f))
  hPutStrLn outHandle ("Zdds0 says: " ++ show (validViaDd myknsZs0 f) ++ "\n")
  hPutStrLn outHandle ("Zddf0 says: " ++ show (validViaDd myknsZf0 f) ++ "\n")
  hPutStrLn outHandle ("Zddf0s0 says: " ++ show (validViaDd myknsZf0s0 f) ++ "\n")
doJob outHandle False mykns myknsZ myknsZs0 myknsZf0 myknsZf0s0 (ValidQ f) = do
  hPutStrLn outHandle $ "Is " ++ ppForm f ++ " valid on the given structure?\n"
  vividPutStrLn ("Bdd says: " ++ show (validViaDd mykns f) ++ "\n")
  vividPutStrLn ("Zdd says: " ++ show (validViaDd myknsZ f) ++ "\n")
  hPutStrLn outHandle ("f in bdd form: " ++ texDdB (bddOf mykns f))
  vividPutStrLn ("Zdds0 says: " ++ show (validViaDd myknsZs0 f) ++ "\n")
  vividPutStrLn ("Zddf0 says: " ++ show (validViaDd myknsZf0 f) ++ "\n")
  vividPutStrLn ("Zddf0s0 says: " ++ show (validViaDd myknsZf0s0 f) ++ "\n")
doJob outHandle True mykns myknsZ myknsZs0 myknsZf0 myknsZf0s0 (WhereQ f) = do
  hPutStrLn outHandle $ "At which states is $" ++ texForm (simplify f) ++ "$ true? $"
  --let states = map tex (whereViaBdd mykns f)
  --hPutStrLn outHandle $ intercalate "," states
  --hPutStrLn outHandle "$\n"
doJob outHandle False mykns myknsZ myknsZs0 myknsZf0 myknsZf0s0 (WhereQ f) = do
  hPutStrLn outHandle $ "At which states is " ++ ppForm f ++ " true?"
  --mapM_ (vividPutStrLn.show.map(\(P n) -> n)) (whereViaBdd mykns f)
  --putStr "\n"

getInputAndSettings :: IO (String,[String])
getInputAndSettings = do
  args <- getArgs
  case args of
    ("-":options) -> do
      input <- getContents
      return (input,options)
    (filename:options) -> do
      input <- readFile filename
      return (input,options)
    _ -> do
      name <- getProgName
      mapM_ (hPutStrLn stderr)
        [ infoline
        , "usage: " ++ name ++ " <filename> {options}"
        , "       (use filename - for STDIN)\n"
        , "  -tex   generate LaTeX code\n"
        , "  -show  write to /tmp, generate PDF and show it (implies -tex)\n" ]
      exitFailure

vividPutStrLn :: String -> IO ()
vividPutStrLn s = do
  setSGR [SetColor Foreground Vivid White]
  putStrLn s
  setSGR []

infoline :: String
infoline = "SMCDEL " ++ showVersion version ++ " -- https://github.com/jrclogic/SMCDEL\n"

texPrelude, texEnd :: String
texPrelude = unlines [ "\\documentclass[a4paper,12pt]{article}",
  "\\usepackage{amsmath,amssymb,tikz,graphicx,color,etex,datetime,setspace,latexsym}",
  "\\usepackage[margin=2cm]{geometry}",
  "\\usepackage[T1]{fontenc}", "\\parindent0cm", "\\parskip1em",
  "\\usepackage{hyperref}",
  "\\hypersetup{pdfborder={0 0 0}}",
  "\\title{Results}",
  "\\author{\\href{https://github.com/jrclogic/SMCDEL}{SMCDEL}}",
  "\\begin{document}",
  "\\maketitle" ]
texEnd = "\\end{document}"
