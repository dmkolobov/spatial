{-# LANGUAGE TemplateHaskell, 
             DeriveFunctor, 
             DeriveTraversable, 
             KindSignatures, 
             TypeFamilies, 
             TypeOperators #-}

module Index where

import Prelude hiding (drop, last, length, splitAt, take, zip, any, map, sum, concatMap)

import Data.Vector

import Data.Functor.Foldable 
import Data.Functor.Base hiding (head)
import Data.Functor.Foldable.TH

import Data.Ord

import Data.Vector.Algorithms.Heap

import Control.Monad.ST

data Node k v = Leaf (Vector ( k , v ))
              | Tree k (Vector (Node k v)) 
              deriving Show 

makeBaseFunctor ''Node  

unsafeLeafEntries :: Node k v -> Vector ( k , v ) 
unsafeLeafEntries (Leaf entries) = entries

unsafeSubtrees :: Node k v -> Vector (Node k v) 
unsafeSubtrees (Tree _ subtrees) = subtrees

alphabet = "abcdefghcijklmnopqrstuvwxyz" 

leaf :: Int -> Int -> Node Int Char 
leaf n i = Leaf . slice (n * i) n . imap (,) $ fromList alphabet

l1 = leaf 3 0 
l2 = leaf 3 1 
l3 = leaf 3 2 

l4 = leaf 3 3 
l5 = leaf 3 4 
l6 = leaf 3 5

l7 = leaf 3 6 
l8 = leaf 3 7

t1 :: PageTree Int Char
t1 = PageTree 2 5 . mkTree . singleton $ Leaf (singleton (26,'z'))

data PageTree k v = PageTree { nodeCap :: Int 
                             , pageCap :: Int 
                             , root    :: Node k v } deriving Show


largestKey :: Node k v -> k 
largestKey (Leaf entries) = fst $ last entries 
largestKey (Tree k _)     = k

mkTree :: Ord k => Vector (Node k v) -> Node k v 
mkTree subtrees
  = runST 
  $ do 
      mv <- thaw subtrees 
      sortBy (comparing largestKey) mv 
      v <- freeze mv
      return $ Tree (largestKey $ last v) v 

data Insert k v = Into { entries :: Vector ( k , v ) 
                       , entry   :: ( k , v ) 
                       }
                | Modify { lk    :: k
                         , node  :: Vector (Node k v) 
                         , pos   :: Int 
                         , inner :: Maybe (Insert k v)
                         }

makeBaseFunctor ''Insert

insertWorker :: Ord k => Int -> Int -> k -> v -> Node k v -> Overflow k v 
insertWorker order cap k v = hylo (conjF order cap) (insertU k v)

insert :: Ord k => PageTree k v -> ( k , v ) -> PageTree k v 
insert (PageTree order cap root) ( k , v )
  = case insertWorker order cap k v root of 
      Left  root' -> PageTree order cap 
                   $ case root' of 
                       leaf@(Leaf _)          -> leaf
                       tree@(Tree _ subtrees) -> case splitAt (length subtrees `div` 2) subtrees of 
                                                   (l , r) -> mkTree 
                                                            . fromList 
                                                            $ [ mkTree l , mkTree r  ]
      Right root' -> PageTree order cap root'

insertU :: Ord k => k -> v -> Node k v -> InsertF k v (Node k v)
insertU key val node 
  = case node of 
      Leaf entries    -> IntoF entries ( key , val ) 
      Tree k subtrees -> let 
                           i = maybe (length subtrees - 1) id 
                             $ findIndex ((key <=) . largestKey) subtrees 
                         in 
                           ModifyF k subtrees i $ Just (subtrees ! i)

type Overflow k v = Either (Node k v) (Node k v)

addEntry :: Ord k => Vector ( k , v ) -> ( k , v ) -> Vector ( k , v ) 
addEntry v e = runST 
             $ do 
                 mv <- thaw $ snoc v e
                 sortBy (comparing fst) mv 
                 freeze mv

conjF :: Ord k => Int -> Int -> InsertF k v (Overflow k v) -> Overflow k v 
conjF order cap q 
  | IntoF entries entry <- q 
    = let 
        n = length entries 
      in 
        (if n < cap then Right else Left) . Leaf $ addEntry entries entry

  | ModifyF k subtrees i overflow <- q
    = case overflow of 
        -- no update
        Nothing -> Right $ Tree k subtrees
        -- there is an update bubbling up
        Just up -> case up of 
                     -- child was modified with no overflow
                     Right node -> Right 
                                 . mkTree 
                                 . update subtrees 
                                 $ singleton ( i , node )
                     -- child was modified and overflowed
                     Left node  -> handleOverflow order cap ( update subtrees  $ singleton ( i , node )) node

sliceUp :: Vector a -> Int -> Vector (Vector a) 
sliceUp v k
  = snoc (generate j $ \i -> slice (m * i) m v)
  $ drop (m * j) v

  where 
    n = length v 
    m = n `div` k 
    j = k - 1

mkBranch :: Vector (Node k v) -> Node k v 
mkBranch subtrees = Tree (largestKey $ last subtrees) subtrees

unsafeLeaves :: Int 
             -> Int
             -> Vector (Node k v) 
             -> Overflow k v
unsafeLeaves order cap leaves
  = if n < order 
    then Right . Tree k . map Leaf . sliceUp entries $ n + 1  
    else if m <= cap * order
         then Right . Tree k . map Leaf . sliceUp entries $ n
         else Left  . Tree k . map Leaf . sliceUp entries $ (order + 1) 
  where
    entries = concatMap unsafeLeafEntries leaves 
    k       = fst $ last entries
    n       = length leaves
    m       = length entries

unsafeTrees :: Int 
            -> Vector (Node k v) 
            -> Overflow k v 
unsafeTrees order trees 
  = if m <= order * order 
    then Right . Tree k . map mkBranch . sliceUp subtrees $ n  
    else Left  . Tree k . map mkBranch . sliceUp subtrees $ (order + 1) 
  where 
    subtrees = concatMap unsafeSubtrees trees
    k        = largestKey $ last subtrees 
    n        = length trees 
    m        = length subtrees 

handleOverflow :: Ord k => Int 
                        -> Int 
                        -> Vector (Node k v) 
                        -> Node k v 
                        -> Overflow k v

handleOverflow order cap subtrees node
  = case node of 
      Leaf _   -> unsafeLeaves order cap subtrees 
      Tree _ _ -> unsafeTrees order subtrees

