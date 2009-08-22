{-# LANGUAGE ScopedTypeVariables #-}

import Control.Arrow ((&&&), second, first)
import Control.Monad (filterM, guard)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (intToDigit, isLatin1, isPrint)
import Data.Function (fix)
import Data.List (genericLength, find, group, sort)
import Data.Maybe (isJust, fromJust)
import Data.Monoid (mconcat)
import System.Environment (getArgs)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (readProcess)

import qualified Data.Map as M
import Data.Map (Map)

type Fungifier i = i -> State (Map i String) String

runFungifier :: Fungifier i -> i -> String
runFungifier f n = evalState (f n) M.empty

fungified :: Integral i => i -> String -> State (Map i String) String
fungified n s = do
   m <- get
   case M.lookup n m of
        Just s' -> return s'
        Nothing -> do
           put $ M.insert n s m
           return s

main :: IO ()
main = (getArgs >>=) . mapM_ $ \s -> do
   let n = read s :: Integer
   putStrLn $ runFungifier fungifyNeg n

fungifyNeg, fungify, naiveFungify, easyFungify :: Integral i => Fungifier i
fungifyNeg n | n >= 0    = fungify n
             | otherwise = do
                f <- fungify (-n)
                fungified n $ concat ["0", f, "-"]

fungify n | isEasy n  = easyFungify n
          | otherwise = do
             s <- mapM f $ factors n
             fungified n $ concat s ++ replicate (length s - 1) '*'
 where
  f x@(factor,p) | isEasy (factor^p) = easyFungify (factor^p)
                 | otherwise         =
                    let (m,p') = applySafeMuls x
                     in if factor == m -- p == p' as well
                           then naiveFungifyWith fungify (factor^p)
                           else do
                              fm <- fungify m
                              ff <- fungify (factor ^ p')
                              fungified (factor^p) $ concat [fm, ff, "*"]

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
      let opts = [ findSum isTrivial easies
                 , findSum isEasy    easies
                 , Just (Left maxEasy)
                 ]
          s = case fromJust.fromJust . find isJust $ opts of
                   Left  e -> [f (n-e), f e, return "+"]
                   Right e -> [f (n+e), f e, return "-"]

      ms <- sequence s
      fungified n $ concat ms

 where
   findSum p (e:es) | p (n+e)   = Just $ Right e
                    | p (n-e)   = Just $ Left e
                    | otherwise = findSum p es
   findSum _ [] = Nothing

easyFungify n
   | n < 16                  = fungified n [intToDigit $ fromIntegral n]
   | isLatin1 c && isPrint c = fungified n ['\'', c]
   | otherwise               = error "easyFungify :: not easy"
 where
   c = toEnum . fromIntegral $ n

isEasy, isTrivial :: Integral i => i -> Bool
isTrivial n = n >= 0 &&  n < 16
isEasy    n = n >= 0 && (n < 16 || (n <= m && isLatin1 c && isPrint c))
 where
   m = fromIntegral $ fromEnum (maxBound :: Char)
   c = toEnum . fromIntegral $ n

printables, easies :: Integral i => [i]
printables = filter (isPrint.toEnum.fromIntegral) [0..255]

easies = [0..15] ++ printables

maxEasy :: Integral i => i
maxEasy = 255 -- last nzEasies

safeLast' :: b -> (a -> b) -> [a] -> b
safeLast' x _ [] = x
safeLast' _ f xs = f (last xs)

whileL :: (a -> Bool) -> (a -> a) -> a -> [a]
whileL p f = takeWhile p . iterate f

plainFactors :: Integral i => i -> [i]
plainFactors 0         = [0]
plainFactors n | n < 0 = -1 : plainFactors (-n)
plainFactors n         = unsafePerformIO $ do
   fs <- readProcess "factor" [show n] ""
   return (map (fromIntegral.(read :: String->Integer)) . tail . words $ fs)

factors :: (Integral i, Integral p) => i -> [(i,p)]
factors = lengthGroup . plainFactors

lengthGroup :: (Eq a, Integral l) => [a] -> [(a,l)]
lengthGroup = map (head &&& genericLength) . group
