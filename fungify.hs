{-# LANGUAGE ScopedTypeVariables #-}

import Control.Arrow               ((&&&), second)
import Control.Concurrent          (forkIO)
import Control.Concurrent.MVar     (newEmptyMVar, putMVar, takeMVar)
import Control.Exception           (catch, SomeException, evaluate)
import Control.Parallel.Strategies (parMap, rwhnf)
import Control.Monad               (liftM2, msum)
import Control.Monad.State.Strict  (State, get, put, evalState)
import Data.Char                   (intToDigit, isLatin1, isPrint, isSpace)
import Data.Function               (fix)
import Data.List                   ( find, group, maximumBy, sort, (\\)
                                   , genericLength )
import Data.List.Split             (chunk)
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
              let ast = astOpt . runFungifier fungify . abs $ n
              putStrLn $ showNegAs sty n ast
              go sty xs

           Nothing -> do
              hPutStrLn stderr $ concat ["Ignoring unknown arg '",x,"'"]
              go sty xs

data AST i = Push i
           | Add (AST i) (AST i)
           | Mul (AST i) (AST i)
 deriving Show

data ShowStyle = RPN | Funge

showNegAs :: Integral i => ShowStyle -> i -> AST i -> String
showNegAs sty n = (if n >= 0 then id else showNeg sty) . showAs sty

showNeg :: ShowStyle -> String -> String
showNeg Funge s = concat  ["0", s, "-"]
showNeg RPN   s = unwords ["0", s, "-"]

showAs :: Integral i => ShowStyle -> AST i -> String
showAs Funge = fungeOpt . fungeShow
showAs RPN   = rpnShow

fungeShow, rpnShow :: Integral i => AST i -> String
fungeShow (Push n) | n < 16                  = [intToDigit $ fromIntegral n]
                   | isLatin1 c && isPrint c = ['\'', c]
                   | otherwise               = error "fungeShow :: bad Push"
 where
   c = toEnum . fromIntegral $ n

fungeShow (Add a b) = concat [fungeShow a, fungeShow b, "+"]
fungeShow (Mul a b) = concat [fungeShow a, fungeShow b, "*"]

rpnShow (Push n)  = show n
rpnShow (Add a b) = unwords [rpnShow a, rpnShow b, "+"]
rpnShow (Mul a b) = unwords [rpnShow a, rpnShow b, "*"]

fungeOpt :: String -> String
fungeOpt ('\'':c:xs) =
   let cs = consecutiveChars xs
       l  = length cs
    in if l >= 2
          then ('"' : c: cs) ++ ('"' : fungeOpt (drop (l*2) xs))
          else '\'' : c : take 2 xs ++ fungeOpt (drop 2 xs)
 where
   consecutiveChars = map (head.tail) . takeWhile ((=='\'').head) . chunk 2

fungeOpt (x:xs) = x : fungeOpt xs
fungeOpt []     = []

astOpt :: Integral i => AST i -> AST i
astOpt = snd . until (not.fst) (compressMuls False . snd) . (,) True
 where
   compressMuls changed x@(Mul a b) =
      let ms        = getMuls x
          (del,res) = maximumBy (comparing $ length.fst)
                    . filter (isEasy.snd)
                    . (concatMap.map) (id &&& product)
                    . partitions $ ms

          changed' = changed || del /= [res]

          res' = Push res
       in if null ms
             then compressMuls2 changed Mul a b
             else maybe (True, res')
                        (second (Mul res') . compressMuls changed')
                        (delMuls del x)

   compressMuls changed (Add a b)  = compressMuls2 changed Add a b
   compressMuls changed x@(Push _) = (changed, x)

   compressMuls2 changed f a b =
      let (c,  a') = compressMuls changed a
          (c', b') = compressMuls changed b
       in (c || c', f a' b')

   getMuls (Push n)  = [n]
   getMuls (Mul a b) = getMuls a ++ getMuls b
   getMuls _         = []

   delMuls dels = snd . go dels
    where
      go [] x = ([], Just x)
      go ds x@(Push n) =
         if n `elem` ds
            then (ds \\ [n], Nothing)
            else (ds, Just x)

      go ds (Mul a b) =
         let (ds',  a') = go ds  a
             (ds'', b') = go ds' b
          in (ds'', msum [liftM2 Mul a' b', a', b'])

      go ds x = (ds, Just x)

type Fungifier i = i -> State (Map i (AST i)) (AST i)

runFungifier :: Integral i => Fungifier i -> i -> (AST i)
runFungifier f n =
   if n < 0
      then error "runFungifier :: negative"
      else evalState (f n) M.empty

fungified :: Integral i => i -> AST i -> State (Map i (AST i)) (AST i)
fungified n s = do
   m <- get
   case M.lookup n m of
        Just s' -> return s'
        Nothing -> do
           put $ M.insert n s m
           return s

fungify, naiveFungify, easyFungify :: Integral i => Fungifier i
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
                        [] -> Just maxEasy
                        xs -> Just . fst $ maximumBy (comparing snd) xs
                 ]

          diff = fromJust.fromJust . find isJust $ opts

      a <- f (n - diff)
      b <- f diff
      fungified n $ Add a b

 where
   tryFacCount x =
      case unsafePerformIO . timeOutMicro' 5000 . length . plainFactors $ x of
           Value v -> Just (x, v)
           _       -> Nothing

   findSum p = find (p . (n-))

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

-- All the rest is thanks to Brent Yorgey's article in The.Monad.Reader issue
-- 8, "Generating Multiset Partitions"
type Vec = [Int]
data MultiSet a = MS [a] Vec deriving Show

partitions :: Ord a => [a] -> [[[a]]]
partitions = map (map msToList) . mPartitions . msFromList
 where
   msFromList = uncurry MS . unzip . lengthGroup . sort

   msToList (MS es cs) = concat $ zipWith replicate cs es

   mPartitions (MS elts v) = map (map (MS elts)) $ vPartitions v

   vPartitions v = vPart v (vUnit v)

   vPart v  _ | all (==0) v = [[]]
   vPart v vL =
      [v] : [v':p | v' <- withinFromTo v (vHalf v) vL
                  , p  <- vPart (zipWith (-) v v') v']

   vUnit [] = []
   vUnit [_] = [1]
   vUnit (_:xs) = 0 : vUnit xs

   vHalf :: Vec -> Vec
   vHalf [] = []
   vHalf (x:xs) | (even x)  = (x `quot` 2) : vHalf xs
                | otherwise = (x `quot` 2) : xs

   withinFromTo m' s' e' | s' >| m'  = withinFromTo m' (zipWith min m' s') e'
                         | e' >  s'  = []
                         | otherwise = wFT m' s' e' True True
    where
      wFT [] _ _ _ _ = [[]]
      wFT (m:ms) (s:ss) (e:es) useS useE =
         let start = if useS then s else m
             end = if useE then e else 0
          in [x:xs | x  <- [start,(start-1)..end]
                   , xs <- wFT ms ss es (useS && x==s) (useE && x==e)]

      wFT _ _ _ _ _ = error "partitions :: impossible"

      xs >| ys = and $ zipWith (>) xs ys
