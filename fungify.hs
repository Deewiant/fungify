{-# LANGUAGE PatternGuards, ScopedTypeVariables #-}

import Control.Arrow               ((&&&), second)
import Control.Concurrent          (forkIO)
import Control.Concurrent.MVar     (newEmptyMVar, putMVar, takeMVar)
import Control.Exception           (catch, SomeException, evaluate)
import Control.Parallel.Strategies (parMap, rwhnf)
import Control.Monad               (foldM_, liftM2, msum)
import Control.Monad.Reader        (ReaderT, runReaderT, ask, asks)
import Control.Monad.State.Strict  (State, get, put, evalState)
import Control.Monad.Trans         (lift)
import Data.Char                   (intToDigit, isLatin1, isPrint, isSpace)
import Data.Function               (fix)
import Data.List                   ( find, group, sort, (\\)
                                   , maximumBy, minimumBy, genericLength )
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
main = foldM_ f ([Funge], [Ascii], True) =<< getArgs
 where
   f opts@(styles,sets,best) s | Just n <- maybeRead s = do

      let asts = flip map sets $ \esId ->
             let easySet = getSet esId
              in astOpt (esIsEasy easySet)
               . runFungifier fungify easySet
               . abs $ (n :: Integer)

          showeds = flip map styles $ \sty -> map (showNegAs sty n) asts

      if best
         then mapM_ (putStrLn . minimumBy (comparing length)) showeds
         else mapM_ (mapM_ putStrLn) showeds

      return opts

   f opts ('+':s) = readOpt True  opts s
   f opts s       = readOpt False opts s

   readOpt add   (ss,es,b) "rpn"    = return (addOpt add RPN   ss,  es, b)
   readOpt add   (ss,es,b) "funge"  = return (addOpt add Funge ss,  es, b)
   readOpt add   (ss,es,b) "dc"     = return (addOpt add DC    ss,  es, b)
   readOpt add   (ss,es,b) "ascii"  = return (ss, addOpt add Ascii  es, b)
   readOpt add   (ss,es,b) "latin1" = return (ss, addOpt add Latin1 es, b)
   readOpt add   (ss,es,b) "hex"    = return (ss, addOpt add Hex    es, b)
   readOpt add   (ss,es,b) "dec"    = return (ss, addOpt add Dec    es, b)
   readOpt False (ss,es,_) "best"   = return (ss, es, True)
   readOpt False (ss,es,_) "each"   = return (ss, es, False)
   readOpt _ opts arg = do
      hPutStrLn stderr $ concat ["Ignoring unrecognized option '", arg, "'"]
      return opts

   addOpt True  x xs = xs ++ [x]
   addOpt False x _  =       [x]

-- For GHCi
simple, simpleOpt :: EasySetId -> Integer -> AST Integer
simple         = runFungifier fungify . getSet
simpleOpt esId = astOpt (esIsEasy $ getSet esId) . simple esId

data AST i = Push i
           | Add (AST i) (AST i)
           | Mul (AST i) (AST i)

           -- Generated in post-processing in astOpt
           | DupMul !Int (AST i)
 deriving (Eq, Show)

data ShowStyle = Funge | RPN | DC

showNegAs :: Integral i => ShowStyle -> i -> AST i -> String
showNegAs sty n = (if n >= 0 then id else showNeg sty) . showAs sty

showNeg :: ShowStyle -> String -> String
showNeg Funge s = concat  ["0", s, "-"]
showNeg RPN   s = unwords ["0", s, "-"]
showNeg DC    s = showNeg RPN s

showAs :: Integral i => ShowStyle -> AST i -> String
showAs Funge = fungeOpt . fungeShow
showAs RPN   = fix rpnShowWith
showAs DC    = dcShow

fungeShow, dcShow :: Integral i => AST i -> String
fungeShow (Push n) | n < 16                  = [intToDigit $ fromIntegral n]
                   | isLatin1 c && isPrint c = ['\'', c]
                   | otherwise               = error "fungeShow :: bad Push"
 where
   c = toEnum . fromIntegral $ n

fungeShow (Add a b)    = concat [fungeShow a, fungeShow b, "+"]
fungeShow (Mul a b)    = concat [fungeShow a, fungeShow b, "*"]
fungeShow (DupMul n a) = concat [fungeShow a, repC n ":", repC n "*"]

dcShow (DupMul n a) = unwords [dcShow a, repU n "d", repU n "*"]
dcShow x            = rpnShowWith dcShow x

rpnShowWith :: Integral i => (AST i -> String) -> AST i -> String
rpnShowWith _ (Push n)     = show n
rpnShowWith f (Add a b)    = unwords [f a, f b, "+"]
rpnShowWith f (Mul a b)    = unwords [f a, f b, "*"]
rpnShowWith f (DupMul n a) = unwords [f a, repU n (f a), repU n "*"]

repC, repU :: Int -> String -> String
repC n = concat  . replicate n
repU n = unwords . replicate n

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

astOpt :: Integral i => (i -> Bool) -> AST i -> AST i
astOpt isEasy = expandDup . fixPoint dup . compressMuls
 where
   -- (x^2)^2 is better than x^4
   expandDup (DupMul n a)
      | n > 1 && odd n  = expandDup . DupMul 1 $ DupMul (n `div` 2) a
      | n > 2 && even n = Mul a . expandDup $ DupMul (n-1) a
      | otherwise       = DupMul n (expandDup a)

   expandDup (Mul a b)    = Mul (expandDup a) (expandDup b)
   expandDup (Add a b)    = Add (expandDup a) (expandDup b)
   expandDup x@(Push _)   = x

   dup (Mul (DupMul n a) b) | a =~= b = DupMul (n+1) (dup a)
   dup (Mul a (DupMul n b)) | a =~= b = DupMul (n+1) (dup a)

   dup (Add a b) | a =~= b   = dup $ Mul (Push 2) a
                 | otherwise = Add (dup a) (dup b)
   dup (Mul a b) | a =~= b   = DupMul 1 (dup a)
                 | otherwise = Mul (dup a) (dup b)
   dup x = x

   -- Equality, handles commutativity but nothing else...
   Add a b =~= Add x y = (a =~= x && b =~= y) || (a =~= y && b =~= x)
   Mul a b =~= Mul x y = (a =~= x && b =~= y) || (a =~= y && b =~= x)
   x       =~= y       = x == y

   compressMuls x@(Mul a b) =
      let ms        = getMuls x
          (del,res) = maximumBy (comparing $ length.fst)
                    . filter (isEasy.snd)
                    . (concatMap.map) (id &&& product)
                    . partitions $ ms

          res' = Push res
       in if null ms
             then Mul (compressMuls a) (compressMuls b)
             else maybe res' (Mul res' . compressMuls) (delMuls del x)

   compressMuls (Add a b)  = Add (compressMuls a) (compressMuls b)
   compressMuls x@(Push _) = x
   compressMuls (DupMul _ _) = error "compressMuls :: impossible DupMul"

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

type Fungified i = ReaderT (EasySet i) (State (Map i (AST i))) (AST i)
type Fungifier i = i -> Fungified i

data EasySetId = Ascii | Latin1 | Hex | Dec

data EasySet i =
   ES { esNzEasies    :: [i]         -- "Nonzero easies"
      , esNzEasiesRev :: [i]
      , esMaxEasy     :: i           -- Same as 'last nums'
      , esIsEasies    :: [i -> Bool] -- Prefer numbers matching an earlier one
      , esIsEasy      ::  i -> Bool  -- Equivalent to \x -> any ($x) esIsEasies
      }

getSet :: Integral i => EasySetId -> EasySet i
getSet ident =
   nz $ case ident of
              Latin1 -> numSet 16 +.+ printableSet 256
              Ascii  -> numSet 16 +.+ printableSet 128
              Hex    -> numSet 16
              Dec    -> numSet 10
 where
   nz e@(ES {esIsEasies = ies, esIsEasy = ie}) =
      e{ esIsEasies = map (\p -> \x -> x > 0 && p x) ies
       , esIsEasy   = \x -> x > 0 && ie x }

   printableSet n = let es = filter printable [1..n-1]
                        m  = last es
                     in mk es m (liftM2 (&&) (<m) printable)

   numSet n = mk [1..n-1] n (<n)

   ES es1 _ _ ies1 i1 +.+ ES es2 _ m ies2 i2 =
      let es = es1 ++ es2
       in ES es (reverse es) m (ies1 ++ ies2) (liftM2 (||) i1 i2)

   printable = isPrint . toEnum . fromIntegral

   mk es m p = ES es (reverse es) m [p] p

runFungifier :: Integral i => Fungifier i -> EasySet i -> i -> (AST i)
runFungifier _ _ n | n < 0 = error "runFungifier :: negative"
runFungifier f s n         =
   flip evalState M.empty . flip runReaderT s $ f n

fungified :: Integral i => i -> AST i -> Fungified i
fungified n s = lift $ do
   m <- get
   case M.lookup n m of
        Just s' -> return s'
        Nothing -> do
           put $ M.insert n s m
           return s

fungify, naiveFungify, easyFungify :: Integral i => Fungifier i
fungify n = asks esIsEasy >>= doIt
 where
   doIt isEasy | isEasy n  = easyFungify n
               | otherwise = do
                    s <- mapM f $ factors n
                    fungified n $ foldr1 Mul s

    where
     f x@(factor,p) | isEasy (factor^p) = easyFungify (factor^p)
                    | otherwise         = do
                       maxEasy <- asks esMaxEasy
                       let y@(m,p') = applySafeMuls maxEasy x
                       if x == y
                          then naiveFungifyWith fungify (factor^p)
                          else do
                             fm <- fungify m
                             ff <- fungify (factor ^ p')
                             fungified (factor^p) $ Mul fm ff

applySafeMuls :: Integral i => i -> (i,i) -> (i,i)
applySafeMuls maxEasy x@(factor,_) =
  safeLast' x (second pred) $ whileL (\(n,p) -> n <= maxEasy && p > 1)
                                     (\(n,p) -> (factor*n, p-1))
                                     x

naiveFungify = fix naiveFungifyWith

naiveFungifyWith :: Integral i => Fungifier i -> Fungifier i
naiveFungifyWith f n = do
   ES nzEasies nzEasiesRev maxEasy isEasies isEasy <- ask
   if isEasy n
      then easyFungify n
      else do
         let opts =
                map (flip findSum nzEasies) isEasies
                ++ [ case catMaybes . pMap (tryFacCount.(n-)) $ nzEasiesRev of
                          [] -> Just maxEasy
                          xs -> Just . fst $ maximumBy (comparing snd) xs
                   ]

             diff = fromJust.fromJust . find isJust $ opts

         a <- f (n - diff)
         b <- f diff
         fungified n $ Add a b

 where
   tryFacCount x | x < 0 = Nothing
   tryFacCount x =
      case unsafePerformIO . timeOutMicro' 5000 . length . plainFactors $ x of
           Value v -> Just (x, v)
           _       -> Nothing

   findSum p = find (p . (n-))

easyFungify n = fungified n (Push n)

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
      \(_ :: SomeException) -> do
         terminateProcess pid
         waitForProcess pid
         return undefined

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

fixPoint :: Eq a => (a -> a) -> a -> a
fixPoint f = snd . until (uncurry (==)) ((id &&& f) . snd) . (id &&& f)

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
   vHalf (x:xs) | even x    = (x `quot` 2) : vHalf xs
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

      (>|) = (and .) . zipWith (>)
