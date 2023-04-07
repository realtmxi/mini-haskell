-- The goal is to implement a function for inferring the type of an expression 
-- in a simplified version of Haskell we will call mini Haskell. 

-- Mini Haskell supports the two functions types, integers and booleans, and a small
-- set of primitive operators (functions) over them, +, >, == and not. 
-- The above operators have meanings in mini Haskell that are similar to the equivalent operators in Haskell. 
-- Their types can be written in Haskell syntax as follows:

-- + :: Int -> Int -> Int
-- > :: Int -> Int -> Bool
-- == :: Int -> Int -> Bool
-- not :: Bool -> Bool

-- We assume there is no overloading, so +, > and == are defined to operate only on integers. 
-- Like Haskell, functions are curried in the sense that they take one argument at a time. 
-- For example, the type of + might be written Int -> (Int -> Int) in Haskell syntax.

Task I: monomorphic types inference

Task II: type unification

Task III: polymorphic type inference
