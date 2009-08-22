{-# LANGUAGE ScopedTypeVariables #-}

import Control.Arrow ((&&&), second, first)
import Control.Monad (filterM, guard)
import Data.Char (intToDigit, isLatin1, isPrint)
import Data.Function (fix)
import Data.List (genericLength, find, group, sort)
import Data.Maybe (isJust, fromJust)
import Data.Monoid (mconcat)
import System.Environment (getArgs)

import qualified Data.ListTrie.Patricia.Set.Ord as TS
import Data.ListTrie.Patricia.Set.Ord (TrieSet)

main :: IO ()
main = getArgs >>= mapM_ (putStrLn . fungifyNeg . read)

fungifyNeg, fungify, naiveFungify :: Integral i => i -> String
fungifyNeg n | n < 0     = concat ["0", fungify (-n), "-"]
             | otherwise = fungify n

fungify n | isEasy n  = easyFungify n
          | otherwise = let s = map f $ factors n
                         in concat s ++ replicate (length s - 1) '*'
 where
  f x@(factor,p) | isEasy (factor^p) = easyFungify (factor^p)
                 | otherwise         =
                    let y@(m,p') = splitMul x
                     in if y == x
                           then naiveFungifyWith fungify (m^p)
                           else concat [ fungify m
                                       , fungify (factor^p')
                                       , "*"
                                       ]

splitMul :: Integral i => (i,i) -> (i,i)
splitMul x@(factor,_) =
  safeLast' x (second pred) $ whileL (\(n,p) -> n <= 15 && p > 1)
                                     (\(n,p) -> (factor*n, p-1))
                                     x

naiveFungify = fix naiveFungifyWith

naiveFungifyWith :: Integral i => (i -> String) -> i -> String
naiveFungifyWith f n
   | isEasy n  = easyFungify n
   | otherwise =
      concat $
         case fromJust.fromJust . find isJust $
                 [ findSum isTrivial easies
                 , findSum isEasy    easies
                 , Just (Left maxPrintable)
                 ] of
              Left  e -> [f (n-e), f e, "+"]
              Right e -> [f (n+e), f e, "-"]
 where
   findSum p (e:es) | p (n+e)   = Just $ Right e
                    | p (n-e)   = Just $ Left e
                    | otherwise = findSum p es
   findSum _ [] = Nothing

easyFungify :: Integral i => i -> String
easyFungify n | n < 16                  = [intToDigit $ fromIntegral n]
              | isLatin1 c && isPrint c = ['\'', c]
              | otherwise               = error "easyFungify :: not easy"
 where
   c = toEnum . fromIntegral $ n

isEasy, isTrivial :: Integral i => i -> Bool
isTrivial n = n >= 0 &&  n < 16
isEasy    n = n >= 0 && (n < 16 || (n <= m && isLatin1 c && isPrint c))
 where
   m = fromIntegral $ fromEnum (maxBound :: Char)
   c = toEnum . fromIntegral $ n

maxPrintable :: Integral i => i
maxPrintable = last printables

printables, easies :: Integral i => [i]
printables = filter (isPrint.toEnum.fromIntegral) [0..255]

easies = [0..15] ++ printables

safeLast' :: b -> (a -> b) -> [a] -> b
safeLast' x _ [] = x
safeLast' _ f xs = f (last xs)

whileL :: (a -> Bool) -> (a -> a) -> a -> [a]
whileL p f = takeWhile p . iterate f

plainFactors :: Integral i => i -> [i]
plainFactors 0 = [0]
plainFactors n = f (2 : [3,5 .. n `quot` 2]) n
 where
  f _        1 = []
  f []       x = [x]
  f l@(p:ps) x = let (q,r) = x `quotRem` p
                  in if r == 0
                        then p : f l q
                        else f ps x

factors :: (Integral i, Integral p) => i -> [(i,p)]
factors = lengthGroup . plainFactors

lengthGroup :: (Eq a, Integral l) => [a] -> [(a,l)]
lengthGroup = map (head &&& genericLength) . group
