{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module TreeAutomata
  ( GrammarBuilder
  , Grammar
  , Rhs (..)
  , Nonterm
  , Alphabet
  , Arity

  -- Constructions
  , empty
  , singleton
  , grammar
  , addConstructor
  , wildcard
  , union
  , union'
  , intersection

  -- Transformations
  , epsilonClosure
  , normalize
  , dedup
  , removeUnproductive
  , productive
  , toSubterms
  , fromSubterms

  -- Queries
  , produces
  , subsetOf
  , isEmpty
  , isSingleton
  , isProductive
  , nthSubterm
  , size
  , height
  , start
  , productions
  , rhs
  , alphabet
  , isDeterministic
  ) where

import           Control.DeepSeq
import           Control.Monad.Except
import           Control.Monad.State

import           Data.Either
import           Data.Hashable
import           Data.IORef
import           Data.List hiding (union)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text

import           Debug.Trace

import           System.IO.Unsafe

import           Util

type Nonterm = Text -- Non-terminal names
data Rhs a = Ctor a [Nonterm] | Eps Nonterm deriving (Show, Eq, Ord)
type Prod a = (Nonterm, Rhs a)

-- The second field of `Grammar` is strict so whnf is enough to get real benchmark numbers
data Grammar a = Grammar Nonterm !(Map Nonterm [Rhs a])
type GrammarBuilder a = State Int (Grammar a)

type Alphabet a = Map a [Arity]
type Arity = Int

instance Show (Grammar a) => Show (GrammarBuilder a) where
  show g = show (evalState g 0)

instance (Ord a, Show a) => Show (Grammar a) where
  show (Grammar start prods) = "start: " ++ Text.unpack start ++ "\n" ++ concatMap f (sort $ Map.toList prods)
    where
      f :: (Ord a, Show a) => (Text, [Rhs a]) -> String
      f (lhs, rhs) = unlines (map (g lhs) $ sort rhs)
      g :: Show a => Text -> Rhs a -> String
      g lhs (Ctor c ns) = Text.unpack lhs ++ " → " ++ show c ++ "(" ++ Text.unpack (Text.intercalate ", " ns) ++ ")"
      g lhs (Eps n) = Text.unpack lhs ++ " → " ++ Text.unpack n

instance Eq a => Eq (GrammarBuilder a) where
  g1 == g2 = g1 `subsetOf` g2 && g2 `subsetOf` g1

deriving instance NFData a => NFData (GrammarBuilder a)

-- TODO: Naming context in grammar
instance NFData a => NFData (Grammar a) where
  rnf (Grammar s p) = rnf s `seq` rnf p
instance NFData a => NFData (Rhs a) where
  rnf (Ctor c ns) = rnf c `seq` rnf ns
  rnf (Eps n) = rnf n

instance Hashable a => Hashable (GrammarBuilder a) where
  hashWithSalt s g = hashWithSalt s (evalState g 0)

instance Hashable a => Hashable (Grammar a) where
  hashWithSalt s (Grammar start prods) = s `hashWithSalt` (0::Int) `hashWithSalt` start `hashWithSalt` prods'
    where
      prods' = Map.foldrWithKey (\k v hash -> hash `hashWithSalt` k `hashWithSalt` v) (1::Int) prods

instance Hashable a => Hashable (Rhs a) where
  hashWithSalt s (Ctor ctor args) = s `hashWithSalt` (0::Int) `hashWithSalt` ctor `hashWithSalt` args
  hashWithSalt s (Eps name) = s `hashWithSalt` (1::Int) `hashWithSalt` name

-- | Empty regular tree grammar
empty :: GrammarBuilder a
empty = do
  start <- uniqueStart
  return $ Grammar start (Map.fromList [(start, [])])

-- | Creates a grammar with a single production from the start symbol
-- to the given constant.
singleton :: a -> GrammarBuilder a
singleton c = do
  start <- uniqueStart
  return (Grammar start (Map.fromList [(start, [ Ctor c [] ])]))

-- | Create a grammar with the given start symbol and production rules
grammar :: Nonterm -> Map Nonterm [Rhs a] -> GrammarBuilder a
grammar s ps = return (Grammar s ps)

-- | Given a non-terminal symbol with n arguments, combines n grammars
-- into a single new grammar containing this constructor.
addConstructor :: Eq a => a -> [GrammarBuilder a] -> GrammarBuilder a
addConstructor n gs = do
  s <- uniqueStart
  gs' <- sequence gs
  return (Grammar s $ Map.insertWith (++) s [ Ctor n (map start gs') ] (Map.unionsWith (++) (map productions gs')))

-- | Creates a grammar with all possible terms over a given signature
wildcard :: Alphabet a -> GrammarBuilder a
wildcard ctxt = do
  start <- uniqueStart
  return (Grammar start (Map.fromList [(start, [Ctor c (replicate i start) | (c, is) <- Map.toList ctxt, i <- is])]))

type RenameMap = Map ([Nonterm],[Nonterm]) Nonterm
type ProdMap a = Map Nonterm [Rhs a]

-- | Union of two grammars. A new, unique start symbol is automatically created.
-- If either of the grammars is empty, the other is returned as-is.
union :: Ord a => GrammarBuilder a -> GrammarBuilder a -> GrammarBuilder a
union g1 g2
 | isEmpty g1 = g2
 | isEmpty g2 = g1
 | otherwise = do
     -- This merges equal parts of the grammars, to prevent largely
     -- duplicated production rules in the resulting union.
     g1' <- epsilonClosure g1
     g2' <- epsilonClosure g2
     (ps,rmap) <- go [start g1'] [start g2'] g1' g2' Map.empty Map.empty
     return (Grammar (rmap Map.! ([start g1'],[start g2'])) ps)
 where
   go :: Ord a => [Nonterm] -> [Nonterm] -> Grammar a -> Grammar a -> ProdMap a -> RenameMap -> State Int (ProdMap a, RenameMap)
   go ns1 ns2 g1@(Grammar _ p1) g2@(Grammar _ p2) res rmap = case Map.lookup (ns1,ns2) rmap of
     Just n -> return (res,rmap)
     Nothing -> do
       n <- uniqueNt
       let rmap' = Map.insert (ns1,ns2) n rmap
       -- N1  -> foo(A1 ,B1 ) | bar(B1)                               in G1
       -- N1' -> foo(A1',B1') | biz(B1')                              in G1
       -- N2  -> foo(A2, B2) | baz(B2)                                in G2
       -- N1xN1'xN2 -> foo(A1xA1'xA2, B1xB1'xB2) | bar(B1) | bar(B2)  in G3
       let prods = Map.fromListWith (\(ns1,ns2) (ns1',ns2') -> (ns1 ++ ns1', ns2 ++ ns2'))
                   $ map fromCtor
                   $ concat [ Left <$> p1 Map.! n1 | n1 <- ns1 ] ++ concat [ Right <$> p2 Map.! n2 | n2 <- ns2 ]
       foldM (\(ps,rmap) (c,(s1,s2)) -> case (transpose s1, transpose s2) of
                 -- TODO: clean up code duplication
                 (s1,[]) -> do
                   (ps',rmap') <- foldM (\(ps,rmap) ns1 -> go ns1 [] g1 g2 ps rmap) (ps,rmap) s1
                   let subterms = map (\ns -> rmap' Map.! (ns,[])) s1
                   return (Map.insertWith (++) n [(Ctor c subterms)] ps',rmap')
                 ([],s2) -> do
                   (ps',rmap') <- foldM (\(ps,rmap) ns2 -> go [] ns2 g1 g2 ps rmap) (ps,rmap) s2
                   let subterms = map (\ns -> rmap' Map.! ([],ns)) s2
                   return (Map.insertWith (++) n [(Ctor c subterms)] ps',rmap')
                 (s1,s2) -> do
                   -- Transpose reorders the subterms by columns so they can be
                   -- merged. Look at the example of `foo`.
                   -- transpose [ [A1,B1], [A1',B1'] ] == [ [A1,A1'], [B1,B1'] ]
                   -- transpose [ [A2,B2]            ] == [ [A2]    , [B2]     ]
                   let ss = zip s1 s2
                   (ps',rmap') <- foldM (\(ps,rmap) (ns1,ns2) -> go ns1 ns2 g1 g2 ps rmap) (ps,rmap) ss
                   let subterms = map (rmap' Map.!) ss
                   return (Map.insertWith (++) n [(Ctor c subterms)] ps',rmap')
             ) (res,rmap') (Map.toList prods)
   fromCtor :: Either (Rhs a) (Rhs a) -> (a,([[Nonterm]],[[Nonterm]]))
   fromCtor (Left (Ctor c ns)) = (c,([ns],[]))
   fromCtor (Right (Ctor c ns)) = (c,([],[ns]))
   -- TODO: can we properly treat epsilon rules?
   fromCtor _ = error "epsilon"

-- | Union of a list of grammars. This simply iterates over the list,
-- using `union` on each pair and `empty` for the base case.
union' :: Ord a => [GrammarBuilder a] -> GrammarBuilder a
union' = foldr union empty

-- | Returns the intersection of the two given grammars.
-- The intersection is taken by taking the cross products of 1)
-- the non-terminals, 2) the start symbols and 3) the production
-- rules. Intuitively, this runs both grammars in parallel.
intersection :: Eq a => GrammarBuilder a -> GrammarBuilder a -> GrammarBuilder a
intersection g1 g2 = do
  Grammar s1 p1 <- g1
  Grammar s2 p2 <- g2
  let
    intersectNonterm :: Nonterm -> Nonterm -> Nonterm
    intersectNonterm n1 n2 = Text.concat [n1, "⨯", n2]
    prods = [(intersectNonterm n1 n2, [Ctor c1 (zipWith intersectNonterm x1 x2) | Ctor c1 x1 <- r1, Ctor c2 x2 <- r2, c1 == c2] ++
               [Eps (intersectNonterm x n2) | Eps x <- r1] ++ [Eps (intersectNonterm n1 x) | Eps x <- r2])
            | (n1, r1) <- Map.toList p1, (n2, r2) <- Map.toList p2]
  normalize $ epsilonClosure $ return $ Grammar (intersectNonterm s1 s2) (Map.fromList prods)

-- | Takes the epsilon closure of a grammar.
epsilonClosure :: GrammarBuilder a -> GrammarBuilder a
epsilonClosure g = do
  Grammar s p <- g
  let
    close name = [r | r@(Ctor _ _) <- concatMap (fromJust . flip Map.lookup p) (reach name)]
    reach :: Nonterm -> [Nonterm]
    reach name = Set.toList $ execState (epsReach name) Set.empty where
      epsReach :: Nonterm -> State (Set Nonterm) ()
      epsReach n = do
        r <- get
        unless (Set.member n r) $ do
          put (Set.insert n r)
          sequence_ [epsReach k | Eps k <- Map.findWithDefault (error ("Nonterm " ++ show n ++ " not in the grammar")) n p]
  return (Grammar s (Map.mapWithKey (\k _ -> close k) p))

-- | Deduplicates a grammar by removing duplicate production rules.
dedup :: Ord a => GrammarBuilder a -> GrammarBuilder a
dedup g = do
  Grammar start prods <- g
  return (Grammar start (Map.map (nub . sort) prods))

-- | Removes productions for empty non-terminals
dropEmpty :: GrammarBuilder a -> GrammarBuilder a
dropEmpty g = do
  Grammar s p <- g
  let
    filterProds = filter (all (`Set.member` nonEmpty) . rhsNonterms)
    nonEmpty = execState (mapM_ f nulls) Set.empty
    invMap = Map.fromList $
             map (\xs -> (snd (head xs), nub $ sort $ map fst xs)) $
             groupBy (\a b -> snd a == snd b) $
             sortBy (\a b -> snd a `compare` snd b)
             [(l, x) | (l, r) <- Map.toList p, x <- concatMap rhsNonterms r]
    nulls = nub $ sort [l | (l, r) <- Map.toList p, Ctor _ [] <- r]
    f :: Nonterm -> State (Set Nonterm) ()
    f n = do r <- get
             unless (Set.member n r) $
               when (any (all (`Set.member` r) . rhsNonterms) (case Map.lookup n p of Just x -> x)) $ do
                 put (Set.insert n r)
                 sequence_ [f x | x <- Map.findWithDefault [] n invMap]
  return (Grammar s (Map.map filterProds (Map.filterWithKey (\k _ -> Set.member k nonEmpty) p)))

-- | Removes productions that are not reachable form the start
dropUnreachable :: GrammarBuilder a -> GrammarBuilder a
dropUnreachable g = do
  Grammar s p <- g
  let
    reachables = execState (f s) Set.empty
    f :: Nonterm -> State (Set Nonterm) ()
    f n = do r <- get
             unless (Set.member n r) $ do
               put (Set.insert n r)
               sequence_ [mapM_ f (rhsNonterms x) | x <- fromMaybe (error ("Nonterm " ++ show n ++ " not in the grammar")) (Map.lookup n p)]
  return $ Grammar s (Map.filterWithKey (\k _ -> Set.member k reachables) p) where

-- | Removes useless productions.
-- We drop unreachable first because that plays better with laziness.
-- But we also drop unreachable after droping empty, because the empty may lead to unreachable.
normalize :: GrammarBuilder a -> GrammarBuilder a
normalize = dropUnreachable . dropEmpty . dropUnreachable

-- | Removes all nonproductive non-terminals from the given grammar.
removeUnproductive :: GrammarBuilder a -> GrammarBuilder a
removeUnproductive g = do
  Grammar start prods <- g
  prodNs <- fmap productive g
  return (Grammar start (Map.filterWithKey (\k _ -> k `Set.member` prodNs) prods))

-- | Returns all productive nonterminals in the given grammar.
productive :: Grammar a -> Set Nonterm
productive (Grammar _ prods) = execState (go prods) p where
  p = Set.fromList [ n | (n, rhss) <- Map.toList prods, producesConstant rhss]
  producesConstant :: [Rhs a] -> Bool
  producesConstant = isJust . find (\r -> case r of Ctor _ [] -> True; _ -> False)
  filter :: [Rhs a] -> Set Nonterm -> Bool
  filter rhss p = case rhss of
    (Ctor _ args : rhss) -> if and (map (`Set.member` p) args) then True else filter rhss p
    (Eps nonterm : rhss) -> if Set.member nonterm p then True else filter rhss p
    [] -> False
  go :: Map Nonterm [Rhs a] -> State (Set Nonterm) ()
  go prods = do p <- get
                let p' = Set.union p $ Set.fromList [ n | (n, rhss) <- Map.toList prods, filter rhss p ]
                put p'
                if p == p' then return () else go prods

-- | Destructs a grammar into a list of (N, [G]) tuples where N is a
-- non-terminal and [G] is a list of grammars, with each grammar G in
-- this tuple having a subterm of N as start symbol.
toSubterms :: GrammarBuilder a -> [(a,[GrammarBuilder a])]
toSubterms (epsilonClosure -> b) =
  let Grammar s ps = evalState b 0
  in [ (c,[nthSubterm n m b | (_,m) <- zip ts [0..]]) | (Ctor c ts,n) <- zip (fromMaybe [] (Map.lookup s ps)) [0..] ]

-- | The opposite of `toSubterms`, i.e., given such a list of tuples,
-- rebuilds the original grammar.
fromSubterms :: Ord a =>  [(a, [GrammarBuilder a])] -> GrammarBuilder a
fromSubterms = epsilonClosure . foldr (\(c, gs) g -> union (addConstructor c gs) g) empty

-- | Returns true iff the grammar can construct the given constant.
produces :: Ord a => GrammarBuilder a -> a -> Bool
produces g n = any (elem n) (Set.map (\p -> [ c | Ctor c [] <- fromJust $ Map.lookup p prods]) (productive (Grammar s prods))) where
  Grammar s prods = evalState g 0

data Constraint = Constraint (Nonterm, Nonterm) | Trivial Bool deriving (Show)
type ConstraintSet = Map (Nonterm,Nonterm) [[Constraint]]

-- | Test whether the first grammar is a subset of the second, i.e. whether
-- L(g1) ⊆ L(g2).
subsetOf :: Eq a => GrammarBuilder a -> GrammarBuilder a -> Bool
g1 `subsetOf` g2 = solve (s1,s2) $ generate Map.empty (Set.singleton (s1,s2)) where
  Grammar s1 p1 = evalState (epsilonClosure g1) 0
  Grammar s2 p2 = evalState (epsilonClosure g2) 0
  -- Solves the generated set of constraints.
  solve :: (Nonterm, Nonterm) -> ConstraintSet -> Bool
  solve pair constraints = case Map.lookup pair constraints of
    Just deps -> all (any (\dep -> case dep of Trivial t -> t; Constraint p -> solve p constraints)) deps
    Nothing -> True
  -- Generate constraints of the form S ⊆ S' iff (A⊆A' ∨ A⊆B') ∧ (B⊆A' ∨ B⊆B') ∧ (True)
  -- for two production rules S -> foo(A) | foo(B) | c and S' -> foo(A') | foo(B') | c. This constraint is stored in a
  -- ConstraintSet with key (S,S') and value [[Constraint ("A","A'"),Constraint ("A","B'")],...]. False results are
  -- skipped as an optimization.
  generate :: ConstraintSet -> Set (Nonterm,Nonterm) -> ConstraintSet
  generate constraints toTest = if Set.null toTest
    then constraints
    else let
      (a1,a2) = Set.elemAt 0 toTest
      toTest' = Set.deleteAt 0 toTest
      dependencies = map (map (\c -> case c of
                                  Trivial t -> Trivial t
                                  Constraint pair -> if pair `elem` Map.keys constraints || pair == (a1,a2)
                                    then Trivial True
                                    else Constraint pair)) $ shareCtor a1 a2
      -- Insert dependencies into the map, regardless of whether there are any. Empty dependencies
      -- are taken care of properly by `solve`.
      constraints' = Map.insert (a1,a2) dependencies constraints
      -- Insert any untested pair (a,b) into toTest.
      toTest'' = foldl (foldl (\toTest dep -> case dep of
                           Constraint pair | pair `notElem` Map.keys constraints' -> Set.insert pair toTest
                           _ -> toTest)) toTest' dependencies
    in generate constraints' toTest''
  -- Given two nonterminals, e.g. S -> foo(A) | foo(B) | c and S' -> foo(A') | foo(B') | c, this function pairs
  -- all constructors creating constraints of the form [[A⊆A' ∨ A⊆B' ∨ False],[B⊆A' ∨ B⊆B' ∨ False],[False ∨ False ∨ True].
  -- As an optimization, False results are skipped entirely, creating instead [[A⊆A' ∨ A⊆B'],[B⊆A' ∨ B⊆B'],[True]
  shareCtor :: Nonterm -> Nonterm -> [[Constraint]]
  shareCtor a1 a2 = [ [ r | r2 <- p2 Map.! a2, r <- match r1 r2 ] | r1 <- p1 Map.! a1 ]
  -- Given two constructors, this function creates the actual constraints:
  -- 1. If two constants are identical, i.e. c and c from the example above, this is trivially true.
  -- 2. If two constructors `foo` are found of equal arity, the constraint is formed pair-wise of their subterms.
  -- 3. If none of these cases apply, then this is trivially false. As an optimization, false results are not actually
  --    inserted in the list but rather skipped entirely.
  match :: Eq a => Rhs a -> Rhs a -> [Constraint]
  match r1 r2 = case (r1, r2) of
    (Ctor c []  , Ctor c' []   ) | c == c' -> [Trivial True]
    (Ctor c args, Ctor c' args') | c == c' && eqLength args args' -> zipWith (\a1 a2 -> Constraint (a1,a2)) args args'
    (Eps e      , Eps e'       ) -> [Constraint (e,e')]
    _                            -> [Trivial False]

-- | Test whether the given grammar generates the empty language.  In
-- regular tree automata, emptiness can be tested by computing whether
-- any reachable state is a finite state. In a regular tree grammar,
-- this comes down to computing whether the start symbol is
-- productive.
isEmpty :: GrammarBuilder a -> Bool
isEmpty g = not (isProductive s g') where
  g' = evalState g 0
  s = start g'

-- | Tests whether the given grammar produces a single term. This can
-- be tested by checking that every non-terminal symbol has no
-- alternative productions, and that the start symbol is productive.
isSingleton :: GrammarBuilder a -> Bool
isSingleton g = isProductive s (Grammar s ps) && noAlts where
  Grammar s ps = evalState (normalize (epsilonClosure g)) 0
  noAlts = and (map (\rhss -> length rhss <= 1) (Map.elems ps))

-- | Tests whether the given nonterminal is productive in the given
-- grammar.
isProductive :: Nonterm -> Grammar a -> Bool
isProductive n g = Set.member n (productive g)

-- | Returns a grammar where the start symbol points to the m-th
-- subterm of the n-th production of the original start symbol.
-- If either index is out of bounds, the original grammar is returned.
nthSubterm :: Int -> Int -> GrammarBuilder a -> GrammarBuilder a
nthSubterm n m g = do
  Grammar s ps <- g
  let prods = fromMaybe [] (Map.lookup s ps)
  if n >= length prods
    then g
    else
      let Ctor _ args = prods !! n
      in if m >= length args
           then g
           else return (Grammar (args !! m) ps)

-- | The size of a regular tree grammar is defined as SUM_(A∈N)(SUM_(A→α) |Aα|).
size :: GrammarBuilder a -> Int
size g = Map.foldr (\rhss acc -> foldr (\rhs acc -> 1 + sizeRhs rhs acc) acc rhss) 0 ps where
  Grammar _ ps = evalState g 0

-- | The size of a right hand side.
sizeRhs :: Rhs a -> Int -> Int
sizeRhs (Ctor _ args) acc = acc + length args
sizeRhs (Eps _) acc = acc + 1

-- | The height of a regular tree grammar is defined as the number of production rules.
height :: GrammarBuilder a -> Int
height g = Map.foldr (\rhss acc -> acc + length rhss) 0 ps where
  Grammar _ ps = evalState g 0

-- | Returns the start symbol of the given grammar.
start :: Grammar a -> Nonterm
start (Grammar s _) = s

-- | Returns the productions of the given grammar.
productions :: Grammar a -> Map Nonterm [Rhs a]
productions (Grammar _ ps) = ps

-- | Returns the right hand sides of the given non-terminal symbol in
-- the given grammar.
rhs :: Grammar a -> Nonterm -> [Rhs a]
rhs (Grammar _ ps) n = fromMaybe [] $ Map.lookup n ps

-- | List the names that occur in a right hand side.
rhsNonterms :: Rhs a -> [Nonterm]
rhsNonterms (Ctor _ ns) = ns
rhsNonterms (Eps n) = [n]

-- | Returns the alphabet over which the given grammar operates.
alphabet :: (Ord a, Show a) => GrammarBuilder a -> Alphabet a
alphabet g = Map.foldl go Map.empty p where
  Grammar _ p = evalState g 0
  go :: (Ord a, Show a) => Alphabet a -> [Rhs a] -> Alphabet a
  go acc [] = acc
  go acc (n:ns) = case n of
    Ctor c n -> go (Map.insert c [length n] acc) ns
    Eps _ -> go acc ns

-- | Checks if the given grammar is deterministic. A deterministic
-- grammar has no production rules of the form X -> foo(A) | foo(A').
isDeterministic :: Eq a => GrammarBuilder a -> Bool
isDeterministic g = all (\rhss -> eqLength (nubBy determinicity rhss) rhss) (Map.elems m) where
  -- Nondeterminism may hide in unproductive or unreachable production rules, so we remove those first.
  Grammar _ m = evalState (removeUnproductive (normalize (epsilonClosure g))) 0
  determinicity :: Eq a => Rhs a -> Rhs a -> Bool
  determinicity (Ctor c args) (Ctor c' args') = c == c' && eqLength args args'
  determinicity _ _ = False

fresh :: State Int Int
fresh = do
  x <- get
  put (x+1)
  return x

uniqueStart :: State Int Text
uniqueStart = do
  x <- fresh
  return $ Text.pack ("Start" ++ show x)

uniqueNt :: State Int Text
uniqueNt = do
  x <- fresh
  return $ Text.pack ("Nt" ++ show x)

eqLength :: [a] -> [b] -> Bool
eqLength [] [] = True
eqLength (_:as) (_:bs) = eqLength as bs
eqLength _ _ = False

{-
introduceEpsilons :: Grammar -> Grammar
introduceEpsilons g = Grammar start $ Map.mapWithKey go prodMap where
  Grammar start prodMap  = shrink $ epsilonClosure g
  go :: Text -> [Rhs] -> [Rhs]
  go key prods =
    let isSubsetOf ps1 ps2 = Set.fromList ps1 `Set.isSubsetOf` Set.fromList ps2
        candidates = filter ((`isSubsetOf` prods) . snd) $ filter ((/= key) . fst) $ Map.toList prodMap
        best = last $ sortOn (length . snd) $ (key, []){-have at least one element for last-} : candidates
        ties = filter ((== length (snd best)) . length . snd) candidates
        ties' = sortOn (sum . map countEps . snd) ties
        countEps (Ctor _ []) = 1
        countEps _ = 0
        best' = head (ties' ++ [(key, [])]{-have at least one element for head-})
        msg = "!!! Warning: "++show (length ties)++"("++show (map (sum . map countEps . snd) ties')++") possibilities for '"++show key++"'\n" ++
              "!!! Need: " ++ show (Grammar key (Map.singleton key prods)) ++
              concat ["!!! Have: " ++ show (Grammar k (Map.singleton k p)) | (k, p) <- ties]
        warn = if length ties <= 1 then id else trace msg
    in if length (snd best') <= 1
       then prods
       else warn $ Eps (fst best') : go (Text.concat ["<", key, ">"]) (Set.toList $ Set.fromList prods `Set.difference` Set.fromList (snd best'))

substNamesOrdered :: [[Name]] -> Grammar -> Grammar
substNamesOrdered e g = foldr subst g e

subst :: [Name] -> Grammar -> Grammar
subst (n : ns) g = foldr (`subst1` n) g ns

subst1 :: Name -> Name -> Grammar -> Grammar
subst1 n1 n2 (Grammar s p) = Grammar (substS n1 n2 s) (Map.fromList p') where
  p' = map h $ groupBy f $ sort $ concatMap (substP n1 n2) (Map.toList p)
  f (c1, _) (c2, _) = c1 == c2
  h (xs@((ctor,_):_)) = (ctor, filter (/= Eps ctor) $ nub $ sort $ concatMap snd xs)
  substP n1 n2 (lhs, rhs) = [(substS n1 n2 lhs, nub $ sort $ map (substR n1 n2) rhs)]
  substS n1 n2 s = if n1 == s then n2 else s
  substR n1 n2 (Eps s) = Eps (substS n1 n2 s)
  substR n1 n2 (Ctor c ns) = Ctor c (map (substS n1 n2) ns)

eqvClasses' :: Map Int Name -> Map Int [(Int, [Int])] -> Map Int{-old name-} Int{-new name-}
eqvClasses' nameInv p = iter f init where
  ps@(p0 : _) = sort (Map.keys p)
  pList = Map.toList p
  init :: Map Int Int
  initBasic = Map.fromList [(p, p0) | p <- ps]
  init = Map.fromList $ concatMap h $ Map.elems init1
  h ns@(n : _) = [(n', n) | n' <- ns]
  init0 :: Map Int{-size-} [Int]
  init0 = Map.fromListWith (++) [(length rhs, [n]) | (n, rhs) <- Map.toList p]
  init1 :: Map [Int]{-ctors-} [Int]
  init1 = Map.fromListWith (++) [(nub $ sort $ map fst rhs, [n]) | (n, rhs) <- Map.toList p]
  f :: Map Int Int -> Map Int Int -- name |-> repesentitive name
  f eqvs = {-trace ("eqvClasses':\n"++unlines [Map.findWithDefault (error "eqvClass'") i nameInv ++ " -> " ++ Map.findWithDefault (error "eqvClasses'") j nameInv | (i, j) <- Map.toList eqvs])-} result where
    inv :: Map [(Int, [Int])] [Int{-old name-}] -- [(ctor, [nt])] |-> member names
    inv = foldr (uncurry (Map.insertWith (++)) . renameProds) Map.empty pList
    renameProds :: (Int, [(Int, [Int])]) -> ([(Int, [Int])], [Int])
    renameProds (n, rhs) = (map renameProd rhs, [n])
    renameProd (c, args) = (c, map renameName args)
    renameName i = Map.findWithDefault (error "eqvClasses'") i eqvs
    result :: Map Int Int
    result = Map.fromList $ concatMap entries (Map.elems inv)
    entries [n] = [(n, n)]
    entries ns@(n : _) = [(n', n) | n' <- ns]

-- TODO: optimize shrink for two states and lots of prods since many TA are like that
-- | Optimizes a grammar by first calculating equivalence classes and then normalizing the grammar.
shrink :: Grammar -> Grammar
shrink g = normalize (eqvClasses {-elimSingleEps2-} g)

eqvClasses :: Grammar -> Grammar
eqvClasses (Grammar s p) = Grammar sFinal pFinal where
  Grammar sEps pEps = {-dedup $-} epsilonClosure (Grammar s p)

  names :: [Name]
  names = nub $ sort $ s : Map.keys p
  nameMap = Map.fromList (zip names [1..])
  nameInv = Map.fromList (zip [1..] names)

  ctors = nub $ sort $ concatMap f (concat (Map.elems pEps)) where
    f (Ctor c _) = [c]
    f _ = []
  ctorMap = Map.fromList (zip ctors [1..])

  mapName n = Map.findWithDefault (error "eqvClasses") n nameMap
  mapCtor c = Map.findWithDefault (error "eqvClasses") c ctorMap
  mapRhs (Ctor c args) = (mapCtor c, map mapName args)
  mapEntry (n, rhs) = (mapName n, map mapRhs rhs)

  p' :: Map Int [(Int, [Int])]
  p' = {-trace ("\n\n\npEps:\n"++pp (Grammar sEps pEps)++"\n\n\n") $-} Map.fromList (map mapEntry (Map.toList pEps))

  renaming :: Map Int{-old name-} Int{-new name-}
  renaming = eqvClasses' nameInv p'

  renamingInv :: Map Int{-new name-} [Int]{-old name-}
  renamingInv = foldr (uncurry (Map.insertWith (++)) . (\(n,n') -> (n', [n]))) Map.empty (Map.toList renaming)

  renameName :: Name -> Name
  renameName n = {-trace ("renameName "++n++" -> "++n') $-} n' where
    n' =
      Map.findWithDefault (error "eqvClasses")
        (Map.findWithDefault (error "eqvClasses")
          (Map.findWithDefault (error "eqvClasses") n nameMap)
          renaming)
        nameInv
  renameRhs (Ctor c args) = Ctor c (map renameName args)
  renameRhs (Eps n) = Eps (renameName n)
  renameEntry :: (Int, [Int]) -> [(Name, [Rhs])]
  renameEntry (n, ns)
    | n /= Map.findWithDefault (error "eqvClasses") n renaming = []
    | otherwise = {-trace ("rhs':"++show rhs')-} [(n', rhs')] where
        n' = Map.findWithDefault (error "eqvClasses") n nameInv
        rhs' :: [Rhs]
        rhs' = filter (/= Eps n') $ nub $ sort $ map renameRhs $ concatMap prods ns'
        ns' :: [Name]
        ns' = map (\n' -> Map.findWithDefault (error "eqvClasses") n' nameInv) ns
        prods :: Name -> [Rhs]
        prods n' = Map.findWithDefault (error "eqvClasses") n' p
  sFinal = renameName s
--  pFinal = Map.fromList (concatMap renameEntry (Map.toList p))
  pFinal = Map.fromList (concatMap renameEntry (Map.toList renamingInv))

-- | Optimizes the grammar by:
-- 
--     * Eliminating non-terminals that have only a single epsilon transition
--     * Eliminating epsilon transitions to single constructor non-terminals
--     * Eliminating non-terminals that are used only once when that one time is an epsilon transition.
elimSingles = iter (elimSingleUse . elimSingleCtor . elimSingleEps)

-- TODO: build map, flatten map, apply to all prods
-- elimSingleEps2 :: Grammar -> Grammar
-- elimSingleEps2 (Grammar s p) = Grammar s' p' where
--   -- initial mappings from single epsilons
--   subst :: Map Name Name
--   subst = Map.fromList [(n, n') | (n, [Eps n']) <- Map.toList p]
--   -- union find algorithm
--   flatten :: [Name] -> Map Name Name -> Map Name Name
--   flatten [] m = m
--   flatten (n : ns) m = flatten ns (flatten' n [] m) where
--     flatten' n ns m
--       | Just n' <- Map.lookup n m = flatten' n' (n:ns) m
--       | otherwise = foldr (\n' -> Map.insert n' n) m ns
--   -- transitive closure of subst
--   subst' :: Map Name Name
--   subst' = flatten (Map.keys subst) subst
--   renameName n = Map.findWithDefault n n subst'
--   renameRhs (Ctor c args) = Ctor c (map renameName args)
--   renameRhs (Eps n) = Eps (renameName n)
--   s' = renameName s
--   p' = Map.fromList [(renameName n, map renameRhs rhs) |
--                       (n, rhs) <- Map.toList p,
--                       Map.notMember n subst' ]

-- | Eliminates non-terminals that have only a single epsilon transition
elimSingleEps :: Grammar -> Grammar
elimSingleEps (Grammar s p) =
  normalize (substNamesOrdered eqvs (Grammar s p))
  where
    eqvs = [[r, n] | (n, [Eps r]) <- Map.toList p]

-- | Eliminates epsilon transitions to single constructor non-terminals
elimSingleCtor :: Grammar -> Grammar
elimSingleCtor (Grammar s p) = normalize (Grammar s (Map.map (map f) p)) where
  f (Eps n) | [c] <- fromJust (Map.lookup n p) = c
  f c = c

-- | Eliminates non-terminals that are used only once when that one time is an epsilon transition
elimSingleUse (Grammar s p) = normalize (Grammar s (Map.map replaceSingleUse p)) where
  replaceSingleUse prods = concatMap replaceSingleUseProd prods
  replaceSingleUseProd (Eps n)
    | n `elem` singleUse = fromJust (Map.lookup n p)
  replaceSingleUseProd x = [x]
  singleUse = filter isSingleUse (Map.keys p)
  isSingleUse n = 1 == sum (map (useCount n) (Map.elems p))
  useCount n prods = sum (map (useCountProd n) prods)
  useCountProd n (Eps n')
    | n == n' = 1
    | otherwise = 0
  useCountProd n (Ctor _ rhs)
    | n `elem` rhs = 2 -- Use 2 since it can't be inlined
    | otherwise = 0

-- Prods is a radix tree on the arguments to a constructor
data Prods = Prods
  [(Ctor, Name)] -- Given no more arguments, this is the constructors and the non-terminals to which they belong
  [(Name, Prods)] -- Given an additional argument, keep traversing down the tree with each Prods
  deriving (Ord, Eq, Show)

makeProds :: Map Name [Rhs] -> Prods
makeProds m = go prods0 where
  prods0 :: [([Name], (Ctor, Name))]
  prods0 = [ (children, (c, n))
           | (n, rs) <- Map.toList m,
             Ctor c children <- rs]
  go :: [([Name], (Ctor, Name))] -> Prods
  go prods =
    Prods
    (concat [ctorAndName | Left ctorAndName <- fac])
    [(head, go rest) | Right (head, rest) <- fac] where
    fac = factorFstHead (sort prods)

factorFst :: (Ord (a, b), Eq a) => [(a, b)] -> [(a, [b])]
factorFst xs = map f (groupByFst xs) where
  f xs@(x : _) = (fst x, map snd xs)

groupByFst :: (Ord (a, b), Eq a) => [(a, b)] -> [[(a, b)]]
groupByFst = groupBy (\x y -> fst x == fst y) . sort

factorFstHead :: (Ord ([a], b), Eq a) => [([a], b)] -> [Either [b] (a, [([a], b)])]
factorFstHead xs =
  map f (groupByFstHead xs) where
  f xs@(([], _) : _) = Left (map snd xs)
  f xs@(x : _) = Right (head (fst x), map g xs)
  g (_ : a, b) = (a, b)

groupByFstHead :: (Ord ([a], b), Eq a) => [([a], b)] -> [[([a], b)]]
groupByFstHead = groupBy (\x y -> maybeHead (fst x) == maybeHead (fst y)) . sort

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(a, b) -> (a, f b))

maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (x : _) = Just x

determinize2 :: Grammar -> Grammar
determinize2 (Grammar s m) =
  loop [] where
  
  prods0 :: Prods
  prods0 = makeProds m
  loop :: [Set Name] -> Grammar --[([Set Name], [(Ctor, Set Name)])]
  loop ss0 = if length ss0 == length ss1
             then Grammar s' (Map.fromList (startEdges ++ res3))
             else loop ss1 where

    res :: [([Set Name], [(Ctor, Name)])]
    res = chooseS [] [prods0]

    res2 :: [([Set Name], [(Ctor, Set Name)])]
    res2 = mapSnd (mapSnd Set.fromList . factorFst) res

    newNt n = "{" ++ intercalate "," (sort $ Set.toList n) ++ "}"

    res3 :: [(Name, [Rhs])]
    res3 =
      factorFst
      [ (newNt nt, Ctor c (map newNt args)) | (args, cnts) <- res2, (c, nt) <- cnts]

    startEdges :: [(Name, [Rhs])]
    startEdges = [(s', [Eps (newNt n) | n <- ss0, s `elem` n])]

    s' = "det:start"

    ss1 = nub $ sort [s | (_, cn) <- res2, (_, s) <- cn]

    chooseS :: [Set Name] -> [Prods] -> [([Set Name], [(Ctor, Name)])]
    chooseS ss prods =
      (case self of (_, []) -> []; _ -> [self]) ++
      (case prods of [] -> []; _ -> r) where
      self :: ([Set Name], [(Ctor, Name)])
      self = (ss, nub $ sort $ concat [c | Prods c _ <- prods])
      children :: [(Name, Prods)]
      children = concat [c | Prods _ c <- prods]
      r :: [([Set Name], [(Ctor, Name)])]
      r = concat [chooseS (ss ++ [s]) (map snd (filter ((`elem` s) . fst) children)) | s <- ss0]
-}
