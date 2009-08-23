{-# LANGUAGE ScopedTypeVariables #-}

import Control.Arrow               ((&&&), second)
import Control.Concurrent          (forkIO)
import Control.Concurrent.MVar     (newEmptyMVar, putMVar, takeMVar)
import Control.Exception           (catch, SomeException, evaluate)
import Control.Parallel.Strategies (parMap, rwhnf)
import Control.Monad               (forM_)
import Control.Monad.State.Strict  (State, get, put, evalState)
import Data.Char                   (intToDigit, isLatin1, isPrint, isSpace)
import Data.Function               (fix)
import Data.List                   (genericLength, find, group, maximumBy)
import Data.Maybe                  (catMaybes, isJust, fromJust)
import Data.Ord                    (comparing)
import System.Environment          (getArgs)
import System.IO                   (hClose, hGetContents, hPutStrLn, stderr)
import System.IO.Unsafe            (unsafePerformIO)
import System.Process              ( createProcess, proc, std_out
                                   , waitForProcess, terminateProcess
                                   , StdStream(CreatePipe)
                                   )
import Test.ChasingBottoms.TimeOut (timeOutMicro', Result(Value))

import qualified Data.Map as M
import Data.Map (Map)

import Prelude hiding (catch)

main :: IO ()
main = go Funge =<< getArgs
 where
   go _   []           = return ()
   go _   ("rpn":xs)   = go RPN xs
   go _   ("funge":xs) = go Funge xs
   go sty (x:xs)       =
      case maybeRead x of
           Just (n :: Integer) -> do
              putStrLn . showWith sty $ runFungifier fungifyNeg n
              go sty xs

           Nothing -> do
              hPutStrLn stderr $ concat ["Ignoring unknown arg '",x,"'"]
              go sty xs

data AST i = Push i
           | Add (AST i) (AST i)
           | Mul (AST i) (AST i)
           | Sub (AST i) (AST i)
 deriving Show

data ShowStyle = RPN | Funge

showWith :: Integral i => ShowStyle -> AST i -> String
showWith Funge = fungeShow
showWith RPN   = rpnShow

fungeShow, rpnShow :: Integral i => AST i -> String
fungeShow (Push n) | n < 16                  = [intToDigit $ fromIntegral n]
                   | isLatin1 c && isPrint c = ['\'', c]
                   | otherwise               = error "fungeShow :: bad Push"
 where
   c = toEnum . fromIntegral $ n

fungeShow (Add a b) = concat [fungeShow a, fungeShow b, "+"]
fungeShow (Sub a b) = concat [fungeShow a, fungeShow b, "-"]
fungeShow (Mul a b) = concat [fungeShow a, fungeShow b, "*"]

rpnShow (Push n)  = show n
rpnShow (Add a b) = unwords [rpnShow a, rpnShow b, "+"]
rpnShow (Sub a b) = unwords [rpnShow a, rpnShow b, "-"]
rpnShow (Mul a b) = unwords [rpnShow a, rpnShow b, "*"]

type Fungifier i = i -> State (Map i (AST i)) (AST i)

runFungifier :: Fungifier i -> i -> (AST i)
runFungifier f n = evalState (f n) M.empty

fungified :: Integral i => i -> AST i -> State (Map i (AST i)) (AST i)
fungified n s = do
   m <- get
   case M.lookup n m of
        Just s' -> return s'
        Nothing -> do
           put $ M.insert n s m
           return s

fungifyNeg, fungify, naiveFungify, easyFungify :: Integral i => Fungifier i
fungifyNeg n | n >= 0    = fungify n
             | otherwise = do
                f <- fungify (-n)
                fungified n $ Sub (Push 0) f

fungify n | isEasy n  = easyFungify n
          | otherwise = do
             s <- mapM f $ factors n
             fungified n $ foldr1 Mul s
 where
  f x@(factor,p) | isEasy (factor^p) = easyFungify (factor^p)
                 | otherwise         =
                    let (m,p') = applySafeMuls x
                     in if factor == m -- p == p' as well
                           then naiveFungifyWith fungify (factor^p)
                           else do
                              fm <- fungify m
                              ff <- fungify (factor ^ p')
                              fungified (factor^p) $ Mul fm ff

applySafeMuls :: Integral i => (i,i) -> (i,i)
applySafeMuls x@(factor,_) =
  safeLast' x (second pred) $ whileL (\(n,p) -> n <= maxEasy && p > 1)
                                     (\(n,p) -> (factor*n, p-1))
                                     x

naiveFungify = fix naiveFungifyWith

naiveFungifyWith :: Integral i => Fungifier i -> Fungifier i
naiveFungifyWith f n
   | isEasy n  = easyFungify n
   | otherwise = do
      let opts = [ findSum isTrivial nzEasies
                 , findSum isEasy    nzEasies
                 , case catMaybes . pMap (tryFacCount.(n-)) $ nzEasiesRev of
                        [] -> Just . Left $ maxEasy
                        xs -> Just . Left . fst $ maximumBy (comparing snd) xs
                 ]

          (op,a,b) = case fromJust.fromJust . find isJust $ opts of
                          Left  e -> (Add, f (n-e), f e)
                          Right e -> (Sub, f (n+e), f e)
      a' <- a
      b' <- b
      fungified n $ op a' b'

 where
   tryFacCount x =
      case unsafePerformIO . timeOutMicro' 5000 . length . plainFactors $ x of
           Value v -> Just (x, v)
           _       -> Nothing

   findSum p (e:es) | p (n+e)   = Just $ Right e
                    | p (n-e)   = Just $ Left e
                    | otherwise = findSum p es
   findSum _ [] = Nothing

easyFungify n = fungified n (Push n)

isEasy, isTrivial :: Integral i => i -> Bool
isTrivial n = n >= 0 &&  n < 16
isEasy    n = n >= 0 && (n < 16 || (n <= m && isLatin1 c && isPrint c))
 where
   m = fromIntegral $ fromEnum (maxBound :: Char)
   c = toEnum . fromIntegral $ n

nzEasies, nzEasiesRev :: Integral i => [i]
nzEasies    = [1..15] ++ filter (isPrint.toEnum.fromIntegral) [16..255]
nzEasiesRev = reverse nzEasies

maxEasy :: Integral i => i
maxEasy = 255 -- last nzEasies

safeLast' :: b -> (a -> b) -> [a] -> b
safeLast' x _ [] = x
safeLast' _ f xs = f (last xs)

whileL :: (a -> Bool) -> (a -> a) -> a -> [a]
whileL p f = takeWhile p . iterate f

plainFactors :: forall i. Integral i => i -> [i]
plainFactors 0         = [0]
plainFactors n | n < 0 = -1 : plainFactors (-n)
plainFactors n         = unsafePerformIO $ do
   (_, Just out, _, pid) <-
      createProcess (proc "factor" [show n]){ std_out = CreatePipe }
   (do fs <- hGetContents out
       mv <- newEmptyMVar
       forkIO $ evaluate (length fs) >> putMVar mv ()
       takeMVar mv
       hClose out
       waitForProcess pid
       return (map ((fromIntegral::Integer->i).read) . tail . words $ fs))
    `catch`
      (\(_ :: SomeException) -> terminateProcess pid >> return undefined)

factors :: (Integral i, Integral p) => i -> [(i,p)]
factors = lengthGroup . plainFactors

lengthGroup :: (Eq a, Integral l) => [a] -> [(a,l)]
lengthGroup = map (head &&& genericLength) . group

pMap :: (a -> b) -> [a] -> [b]
pMap = parMap rwhnf

maybeRead :: Read a => String -> Maybe a
maybeRead s = case reads s of
                   [(x,w)] | all isSpace w -> Just x
                   _                       -> Nothing
