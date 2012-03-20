{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns    #-}
module Math.SetCover
     ( Subsets
     , subsets
     , setCover
     
     , coverable
     , minimumCovers
     , greedyMinCover
     , greedyMinCover1
     , greedyMinCover2
     
     , main
     ) where

import Data.Char
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.ST
import           Control.Monad.Loops
import qualified Data.Bimap                         as BM
import           Data.Bit
import           Data.Bits
import qualified Data.List                          as L
import qualified Data.Set                           as S
import qualified Data.Vector                        as V
import qualified Data.Vector.Generic                as G
import qualified Data.Vector.Generic.Mutable        as M
import qualified Data.Vector.Unboxed.Bit            as U
import qualified Data.Vector.Unboxed.Mutable        as MU
import qualified Data.Vector.Unboxed.Mutable.Bit    as MU

-- An instance of the set cover problem (either the minimization or decision version) is given by 2 data:
-- 
-- 1. a set of elements to be covered
-- 2. a set of subsets which are to be used
-- 
-- internally these are represented as:
--  (1) an array, elements of which are the objects in question.  The elements are used for no purpose other than identifying objects in the solution.  They probably aren't even needed for that.
--  (2) an array of subset names for identifying subsets, and an array of bit vectors, identifying the elements of the universe contained by each subset.

-- |A finite universe of values and a collection of named subsets of that universe
data Subsets u s = Subsets
    { universe      :: !(V.Vector u)
    , subsetNames   :: !(V.Vector s)
    , subsetElems   :: !(V.Vector (U.Vector Bit))
    } deriving Show

instance (NFData u, NFData s) => NFData (Subsets u s) where
    rnf Subsets{..}
        = flip (V.foldr deepseq) universe
        . flip (V.foldr deepseq) subsetNames
        . flip (V.foldr seq) subsetElems
        $ ()

-- internal: provided data must be consistent (equal length lists, all subset elements exist in universe, etc.)
mkSubsets :: Ord u => S.Set u -> [s] -> [S.Set u] -> Subsets u s
mkSubsets universeSet subsetNameList subsets = Subsets{..}
    where
        universe    = V.fromList (S.toList universeSet)
        subsetNames = V.fromList subsetNameList
        subsetElems = V.fromList
            [ U.fromList 
                [ fromBool (S.member x subset)
                | x <- V.toList universe
                ]
            | subset <- subsets
            ]

subsets :: Ord u => S.Set u -> BM.Bimap s (S.Set u) -> Subsets u s
subsets universeSet p = mkSubsets universeSet subsetNameList subsets
    where
        (subsetNameList, subsets) = unzip (BM.assocs p)

-- | simple constructor for instances of the set cover problem; given a collection of named subsets, build a problem instance where the universe is the union of all the subsets and the subsets are the ones given.
-- Does a fair amount of work shuffling thing around though;  probably more than is necessary.
setCover :: Ord u => BM.Bimap s (S.Set u) -> Subsets u s
setCover p = mkSubsets (S.unions subsets) subsetNameList subsets
    where
        (subsetNameList, subsets) = unzip (BM.assocs p)

subset :: Ord u => Int -> Subsets u s -> S.Set u
subset n Subsets{..} = S.fromList (U.select (subsetElems V.! n) universe)

data Solution u s = Solution
    { problem       :: Subsets u s
    , selection     :: U.Vector Bit
    } deriving Show

covering :: Solution u s -> [s]
covering Solution{problem = Subsets{..}, ..}
    = U.select selection subsetNames

isSetCovering :: Solution u s -> Bool
isSetCovering (Solution Subsets{..} selection) =
       U.all toBool (U.unions (V.length subsetElems) (U.select selection subsetElems))

choose :: Int -> Int -> [U.Vector Bit]
choose n k
    | k <= 0    = [U.empty | n == 0]
    | n <= 0    = [U.replicate k 0]
    | otherwise
        =  map (U.cons 0) (choose  n    (k-1))
        ++ map (U.cons 1) (choose (n-1) (k-1))

-- | A brute-force solution of the set-cover decision problem ("does there exist a cover consisting of at most k of the given subsets?").  Returns all such covers, but does so lazily.  Not suitable for any but the smallest problems.
coverable :: Subsets u s -> Int -> [Solution u s]
coverable problem@Subsets{..} = loop (U.replicate n 0) [] 0
    where
        n = V.length universe
        m = V.length subsetElems
        
        toSolution is = runST $ do
            selection <- MU.replicate m 0
            sequence_ [ MU.write selection i 1 | i <- is ]
            fmap (Solution problem) (G.unsafeFreeze selection)
        
        loop !covered !selected !i !k
            | U.and covered = [toSolution selected]
            | k == 0        = []
            | i >= m        = []
            | otherwise     = use_i ++ skip_i
            where
                subset_i = subsetElems V.! i
                use_i  = if U.or (U.difference subset_i covered)
                    then loop (U.union covered subset_i) (i:selected) (i+1) (k-1)
                    else []
                skip_i = loop covered selected (i+1) k


-- | A brute-force solution for the set-cover minimization problem; not suitable for any but the smallest problems.
minimumCovers :: Subsets u s -> [Solution u s]
minimumCovers problem@Subsets{..} = 
    firstSolution (map (coverable problem) [0 .. V.length subsetElems])
    where
        firstSolution [] = []
        firstSolution (x : xs)
            | null x    = firstSolution xs
            | otherwise = x

greedyMinCover :: Subsets u s -> Maybe (Solution u s)
greedyMinCover problem@Subsets{..}
    | n > m     = greedyMinCover1 problem
    | otherwise = greedyMinCover2 problem
    where
        n = V.length universe
        m = V.length subsetElems

-- the standard greedy heuristic; at every step, choose the subset with the most uncovered elements.  currently, 'score' is by far the most costly step.  I've tried actually 'deflating' the problem, but that's actually extremely costly (though it would be much better if I had a version of 'select' that used a vector-mux CPU instruction - does x64 have that?)
greedyMinCover1 :: Subsets u s -> Maybe (Solution u s)
greedyMinCover1 problem@Subsets{..} = runST $ do
    let n = V.length universe
        m = V.length subsetElems
    
    covered  <- MU.replicate n 0
    selected <- MU.replicate m 0
    
    let -- score: O(n)
        score i = do
            i_selected <- MU.read selected i
            if toBool i_selected
                then return 0
                else loop (0 :: Int) 0
            where
                set = subsetElems V.! i
                loop !s !i
                    | i >= n    = return s
                    | otherwise = do
                        c <- MU.readWord covered i
                        loop (s + popCount (U.indexWord set i .&. complement c)) (i + U.wordSize)
        
        -- loop: O(n*m*m)
        loop = do
            allCovered <- MU.allBits 1 covered
            if allCovered
                then return True
                else do
                    Just i <- maximumOnM score [0 .. m - 1]
                    i_selected <- MU.read selected i
                    if toBool i_selected
                        then return False
                        else do
                            MU.write selected i 1
                            MU.unionInPlace covered (subsetElems V.! i)
                            loop
    
    solved <- loop
    
    if solved
        then fmap (Just . Solution problem) (G.unsafeFreeze selected)
        else return Nothing

-- A greedy heuristic favoring cases where the universe is relatively small compared to the number of subsets.  Starts by building a matrix describing the relation "has a common cover" on elements of the universe (at a cost of about n^2 bits), then uses that relation to select the 'least connected' element of the universe at each step and selects a cover for that element.
greedyMinCover2 problem@Subsets{..} = runST $ do
    let n = V.length universe
        m = V.length subsetElems
        
        -- subset of subsets containing x
        mkGrp x = U.generate m (\s -> subsetElems V.! s U.! x)
        -- union of subsets indicated in grp
        mkRel :: U.Vector Bit -> U.Vector Bit
        mkRel grp = U.unions n (U.select grp subsetElems)
    
    let grps :: V.Vector (U.Vector Bit) -- n * m bits
        grps = V.generate n mkGrp
        rels :: V.Vector (U.Vector Bit) -- n * n bits
        rels = V.map mkRel grps
        keys :: U.Vector Int            -- n ints
        keys = U.generate n (\i -> U.countBits (rels V.! i))
    keys <- U.thaw keys
    
    uncovered <- MU.replicate n 1       -- n bits
    selected  <- MU.replicate m 0       -- m bits
    
    let pickGrp grp = maximumOnM score (U.listBits grp)
            where
                score setId = scoreLoop 0 0
                    where
                        set = subsetElems V.! setId
                        scoreLoop !s !i
                            | i >= n                = return (s :: Int, U.length set)
                            | toBool (set U.! i)    = do
                                u_i <- MU.read uncovered i
                                if toBool u_i
                                    then scoreLoop (s+1) (i+1) 
                                    else scoreLoop  s    (i+1)
                            | otherwise             = scoreLoop s (i+1)
        
         -- for each x in 1..m, if x in selectedElems and is uncovered then for each y in rels V.! x, decrement keys V.! y
        adjustKeys [] = return ()
        adjustKeys (x:xs) = do
            u_x <- MU.read uncovered x
            let rel_x = rels V.! x
            when (toBool u_x) (mapM_ adjustKey (U.listBits rel_x))
            adjustKeys xs
        adjustKey y = do
            u_y <- MU.read uncovered y
            when (toBool u_y) $ do
                key_y <- MU.read keys y
                MU.write keys y (key_y - 1)
        
        loop = do
            u <- MU.listBits uncovered
            pick <- minimumOnM (MU.read keys) u
            case pick of
                Nothing -> return (null u)
                Just x -> do
                    selection <- pickGrp (grps V.! x)
                    
                    case selection of
                        Nothing -> return (null u)
                        Just selection -> do
                            MU.differenceInPlace uncovered (subsetElems V.! selection)
                            MU.write selected selection 1
                            
                            let selectedElems = subsetElems V.! selection
                            adjustKeys (U.listBits selectedElems)
                            
                            loop
                            
    
    solved <- loop
    
    if solved
        then fmap (Just . Solution problem) (G.unsafeFreeze selected)
        else return Nothing

testProblem1 :: Subsets Int Int
testProblem1 = setCover $ BM.fromList
    [ (1, S.fromList [1,2,3])
    , (2, S.fromList [2,4])
    , (3, S.fromList [3,4])
    , (4, S.fromList [4,5])
    ]
-- the standard problem for showing worst-case behavior of the greedy heuristic
-- TODO: this can easily be generate faster... do so
testProblem2 :: Int -> Subsets Int String
testProblem2 k = setCover $ BM.fromList (
    [ ("s" ++ show i, S.fromList [2 ^ i + 1 .. 2 ^ (i + 1)])
    | i <- [1 .. k]
    ] ++
    [ ("t0", S.fromList [3, 5 .. 2 ^ (k + 1)])
    , ("t1", S.fromList [4, 6 .. 2 ^ (k + 1)])
    ])
testProblem3 = setCover $ BM.fromList
    [ (w, S.fromList w)
    | w <- words "the quick brown fox jumps over the lazy dog"
    ]
testProblem4 = setCover $ BM.fromList
    [ (w, S.fromList w)
    | w <- words "the quick brown fox jumps over the lazy dog"
        ++ words "the rain in Spain falls mainly in the plain"
        ++ words "I can't hear you unless you knock"
    ]

main = do
    let solve f p = seq (rnf p) $ do
            let n = V.length (universe    p)
                m = V.length (subsetElems p)
            
            putStrLn $ unwords
                [ "universe has", show n, "elems"
                , "and", show m, "subsets"]
            putStrLn $ unwords
                ["solution:", show (fmap covering (f p))]
            
--    solve minimumCovers  testProblem1
--    solve minimumCovers (testProblem2 4)
--    solve minimumCovers  testProblem3
--    solve greedyMinCover testProblem4
--    solve minimumCovers  testProblem4
--    rnf (testProblem2 19) `seq` putStrLn "done"
--    solve greedyMinCover2 (testProblem2 15)
    solve greedyMinCover1 (testProblem2 19)
--    solve minimumCovers (testProblem2 19)
    
--    dict <- fmap words (readFile "/usr/share/dict/words")
--    let p = setCover $ BM.fromList [(w, S.fromList w) | w <- dict, all isLower w]
--    -- solve minimumCovers p
--    mapM_ (print . covering) (coverable p 2)
