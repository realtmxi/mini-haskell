import Data.Maybe


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

-- In mini Haskell, expressions are built from basic values, i.e. integer and boolean constants, 
-- variable identifiers, primitive operators, conditionals and function applications. 
-- User-defined functions are also supported in mini Haskell:

data Expr = Number Int |
            Boolean Bool |
            Id String |
            Prim String |
            Cond Expr Expr Expr |
            App Expr Expr |
            Fun String Expr
                deriving (Eq, Ord, Show)

-- Example: The expression
--                if not (> x y) then x else + y 1
--   is represented in our mini Haskell as follows:
--      Cond (App (Prim "not") (App (App (Prim ">") (Id "x")) (Id "y")))
--           (Id "x")
--           (App (App (Prim "+") (Id "y")) (Number 1))


-- In order to infer the type of an expression we need a representation for types. 
-- The following are our mini Haskell data types:

data Type = TInt |
            TBool |
            TFun Type Type |
            TErr |
            TVar String
               deriving (Eq, Ord, Show)

-- TInt and TBool represent the integer and boolean types, respectively. 
-- The TFun constructor encodes the equivalent of the 'arrow' (->) function type operator in Haskell. 
-- TErr represents a type error: an expression that doesn't type check, 
-- e.g. the expression not 1, will have its type inferred as TErr. 
-- TVar is used to represent type variables. 


-- Note that the type of the 'greater than' operator, >, can be represented in mini Haskell as 
-- TFun TInt (TFun TInt TBool), equivalent to Int -> Int -> Bool in Haskell syntax. 
-- The following table contains the types of each of the primitives operators that
-- maps their identifiers (Strings) to the corresponding types:

type TypeTable = [(String, Type)]

-- primTypes :: TypeTable

primTypes = [("+", TFun TInt (TFun TInt TInt)),
             (">", TFun TInt (TFun TInt TBool)),
             ("==", TFun TInt (TFun TInt TBool)),
             ("not", TFun TBool TBool)]

-- The following function showT display mini Haskell types in the more familiar Haskell syntax.

showT :: Type -> String

showT TInt  
  = "Int"
showT TBool 
  = "Bool"
showT (TFun t t') 
  = "(" ++ showT t ++ " -> " ++ showT t' ++ ")"
showT (TVar a) 
  = a
showT TErr  
  = "Type error"


-- In the absence of type variables and user-defined functions type inference can be done  
-- easily using the following rules:

 -- Constants (Constructors Number, Boolean): The types of the integer and boolean constants are known. 
 -- For example, the type of Number 6 is TInt and the type of Boolean False is TBool.

 -- Identifiers (Constructor Id): The type of an identifier is given by a supplied type environment
 -- which is a table that associates variable identifiers in expressions with types. 

type TEnv = TypeTable 

 -- For example, if the expression is Id "a" and the environment contains a binding
 -- ("a",TInt) then the expression can be inferred to have type TInt. 

 -- Primitives (Constructor Prim): The type of a primitive operator is determined by looking up 
 -- its identifier in the primTypes table above. 
 -- For example, if the expression is Prim "==" the inferred type will be TFun TInt (TFun TInt TBool).

 -- Conditionals (Constructor Cond): For a conditional expression to be correctly typed the type 
 -- of the condition, i.e. the first argument of Cond, must be a boolean (TBool) and the type of
 -- the 'then' and 'else' alternatives, i.e. the second and third arguments of Cond, respectively,
 -- can be any type so long as they are the same. 
 -- If any of these properties is violated then the inferred type of the conditional is TErr; 
 -- otherwise it is the inferred type of either the two alternatives. 

 -- Applications (Constructor App): In the absence of type variables and user-defined functions
 -- the type of a function application can be inferred straightforwardly from the types of its
 -- two components, i.e. the function and argument expressions, computed recursively. 
 -- For the expression to be correctly typed the recursively computed function type must be of the form 
 -- TFun t1 t2 and the recursively computed argument type must be t1. 
 -- If this holds then the application as a whole has type t2. 
 -- In all other cases the expression is incorrectly typed and the inferred type will be TErr.

---------------------- Task I: monomorphic types inference ----------------

-- Implement a function inferMono :: Expr -> TEnv -> Type that given an expression and a
-- type environment, will infer the type of the given expression in the absence of type variables and 
-- user-defined functions using the above rules of inference. 
-- For the case of identifiers, e.g. Id i, a precondition is that there will be 
-- a binding for i in the given type environment.

-- You are allowed to use helper functions to implement inferMono. 

-- The expression given to inferMono is guaranteed to not contain any user-defined functions. 
-- So you do not need a case for the Fun constructor. 

inferMono :: Expr -> TEnv -> Type
inferMono (Number _) _ = TInt
inferMono (Boolean _) _ = TBool
inferMono (Id i) env = case lookup i env of
                         Just t  -> t
                         Nothing -> error "Variable not found in the environment"
inferMono (Prim p) _ = case p of
                         "+" -> TFun TInt (TFun TInt TInt)
                         "-" -> TFun TInt (TFun TInt TInt)
                         "*" -> TFun TInt (TFun TInt TInt)
                         "==" -> TFun TInt (TFun TInt TBool)
                         "<" -> TFun TInt (TFun TInt TBool)
                         "not" -> TFun TBool TBool
                         _ -> error "Unknown primitive"
inferMono (App e1 e2) env = case inferMono e1 env of
                              TFun argType resType ->
                                if argType == inferMono e2 env
                                then resType
                                else TErr
                              _ -> TErr



-- The following are tests cases to test your implementation
-- The test cases consist of expressions 
-- with monomorphic types and their expected types.


env :: TEnv
env = [("b",TBool)]

ex1, ex2, ex3 :: Expr
type1, type2, type3 :: Type

ex1 = Number 9
type1 = TInt
-- inferMono ex1 env should return type1

ex2 = App (Prim "not") (Id "b")
type2 = TBool
-- inferMono ex2 env should return type2

ex3 = App (App (Prim "+") (Boolean True)) (Number 5)
type3 = TErr
-- inferMono ex3 env should return type3

-- ADD MORE TESTS
-- ......
-- ......
------------------------------------------------------

--- 
-- Now we want to generalize inferMono and allow it to infer the type of expressions 
-- involving user-defined functions and type variables. 
-- In our case here we need to know whether two types are unifiable. 
-- For example: suppose that when typing a conditional the 'then' and 'else' alternatives 
-- are inferred to have the (function) types
-- TFun TInt (TVar "a")
--  and
-- TFun (TVar "b") TBool
-- They are clearly not syntactically the same, but they are unifiable, 
-- i.e. by associating the type variable "a" with the type TBool and, "b" with TInt. 
-- Now the two alternatives are consistently typed. 
-- A set of type associations of this sort is called a type unification and substitution. 
-- We will represent it as a list of (String, Type) pairs:

type Sub = TypeTable -- i.e. [(String, Type)]

-- For instance, the substitution above is represented by the list [("a",TBool), ("b",TInt)].

-- The result of the unification of two types will be an object of type Sub, 
-- if a unifying substitution can be found. If not then the unification fails.

-- For instance, can TVar "a" and TFun (TVar "x") (TVar "b"), (TVar "c") and 
-- TFun (TVar "y") (TVar "b"), TFun TInt (TFun TInt TInt) and TFun TInt (TVar "c"),
-- and TVar "x" and TVar "y", be made equal by setting "a", "b" "c", "x", and "y" appropriately?

--inputTypes = [(TVar "a", TFun (TVar "x") (TVar "b")), 
--              (TVar "c", TFun (TVar "y") (TVar "b")),
--              (TFun TInt (TFun TInt TInt),  TFun TInt (TVar "c")), 
--              (TVar "x",  TVar "y")]

-- A possible algorithm for answering the above question does an iterative process that looks at  
-- the first pair and produces a new list of pairs and possibly an assignment for one of the
-- remaining variables.
  
-- The algorithm first examines the type pair (TVar "a", TFun (TVar "x") (TVar "b")) 
-- and iteratively examine the remaining pairs 
--             [(TVar "c", TFun (TVar "y") (TVar "b")),
--              (TFun TInt (TFun TInt TInt),  TFun TInt (TVar "c")), 
--              (TVar "x",  TVar "y")]
-- Next it examines the type pair (TVar "c", TFun (TVar "y") (TVar "b"))
-- and iteratively examine the remaining pairs (replaces TVar "c" by its value)
--             [(TFun TInt (TFun TInt TInt),  TFun TInt (TFun (TVar "y") (TVar "b"))), 
--              (TVar "x",  TVar "y")]
-- Next it examines the type pair ((TFun TInt (TFun TInt TInt),  TFun TInt (TFun (TVar "y") (TVar "b"))))
-- This results in adding the pairs (TInt, TInt) and (TFun TInt TInt,  TFun (TVar "y") (TVar "b")) to the list 
-- and iteratively examine the new remaining pairs 
--             [(TInt, TInt),
--              (TFun TInt TInt,  TFun (TVar "y") (TVar "b")),
--              (TVar "x",  TVar "y")]
-- Next it examines the type pair (TInt, TInt) and discards it 
-- and iteratively examine the remaining pairs 
--             [(TFun TInt TInt,  TFun (TVar "y") (TVar "b")),
--              (TVar "x",  TVar "y")]
-- Next it examines the type pair (TFun TInt TInt,  TFun (TVar "y") (TVar "b"))
-- This results in adding the pairs (TInt, TVar "y") and (TInt,  TVar "b") to the list 
-- and iteratively examine the new remaining pairs 
--             [(TInt,  TVar "x"),
--              (TInt,  TVar "b"),
--              (TVar "x",  TVar "y")]
-- Next it examines the type pair (TInt,  TVar "x") and produces the first pair ("x", TInt)
-- and iteratively examine the remaining pairs 
--             [(TInt,  TVar "b"),
--              (TInt,  TVar "y")]
-- Next it examines the type pair (TInt,  TVar "b") and produces another pair ("b", TInt)
-- and iteratively examine the remaining pairs 
--             [(TInt,  TVar "y")]
-- Next it examines the type pair (TInt,  TVar "y") and produces another pair ("y", TInt)
-- The resulting "substitution" is to replace:
--   TVar "a" with TFun TInt TInt
--   TVar "c" with TFun TInt TInt
--   TVar "x" with TInt
--   TVar "b" with TInt
--   TVar "y" with TInt
-- The algorithm then stops producing 
-- [("a", TFun TInt TInt), ("c", TFun TInt TInt), ("x", TInt), ("b", TInt), ("y", TInt)]. 


-- This an instantiation of Martelli and Montanari unification algorithm which operators on 
-- a list of pairs of types of the form 
-- [(t1, t1'), (t2, t2'), ..., (tn, tn')] and 
-- produces a substitution (Sub) which is initially empty ([]) and it grows as the algorithm proceeds. 
-- The algorithm outputs either a unifying substitution, or a failure. 
-- To unify two types t and t' we initialise the algorithm with the singleton list [(t,t')] and 
-- the empty substitution []


-- To terminate the list of type pairs becomes empty ([]) when the substitution is s 
-- then the unification succeeds and the resulting substitution is s.

-- The unification algorithm must distinguish between a successful unification, which results in
-- a (possibly empty) substitution, and a unification failure. 
-- Thus, the result of the unification is an object of type:  
-- Maybe Sub
unifyAux :: [(Type, Type)] -> Sub -> Maybe Sub
unifyAux [] sub = Just sub
unifyAux ((t1, t2) : ts) sub
  | t1 == t2 = unifyAux ts sub
  | otherwise = case (t1, t2) of
                  (TVar x, _) -> unifyAux (substInPairs x t2 ts) ((x, t2) : sub)
                  (_, TVar x) -> unifyAux (substInPairs x t1 ts) ((x, t1) : sub)
                  (TFun arg1 res1, TFun arg2 res2) -> unifyAux ((arg1, arg2) : (res1, res2) : ts) sub
                  _ -> Nothing

-- Helper function to substitute a type in a list of pairs of types
substInPairs :: String -> Type -> [(Type, Type)] -> [(Type, Type)]
substInPairs x t pairs = [(substInType x t t1, substInType x t t2) | (t1, t2) <- pairs]

-- Helper function to substitute a type in another type
substInType :: String -> Type -> Type -> Type
substInType x t (TVar y) = if x == y then t else TVar y
substInType x t (TFun arg res) = TFun (substInType x t arg) (substInType x t res)
substInType _ _ t = t


unify :: Type -> Type -> Maybe Sub
unify t1 t2 = unifyAux [(t1, t2)] []

---------------------- Task II: type unification ----------------

-- Implement a function unifyTypes :: [(Type, Type)] -> Sub -> Maybe Sub that implements
-- type unification. 
-- You are allowed to use helper functions to implement unifyTypes. 

-- Find the substitution for a type variable in the current substitution
findSub :: String -> Sub -> Maybe Type
findSub x [] = Nothing
findSub x ((y, t):sub)
  | x == y    = Just t
  | otherwise = findSub x sub

-- Apply a substitution to a type
applySub :: Sub -> Type -> Type
applySub sub (TVar x) =
  case findSub x sub of
    Just t  -> t
    Nothing -> TVar x
applySub sub (TFun t1 t2) = TFun (applySub sub t1) (applySub sub t2)
applySub _ t = t

-- Check if a type variable occurs in a type
occursCheck :: String -> Type -> Bool
occursCheck x (TVar y) = x == y
occursCheck x (TFun t1 t2) = occursCheck x t1 || occursCheck x t2
occursCheck _ _ = False

-- Unify two types given a current substitution
unifyTypes :: [(Type, Type)] -> Sub -> Maybe Sub
unifyTypes [] sub = Just sub
unifyTypes ((t1, t2):ts) sub
  | t1 == t2 = unifyTypes ts sub
unifyTypes ((TVar x, t):ts) sub
  | not (occursCheck x t) = unifyTypes (map (\(t1, t2) -> (applySub [(x, t)] t1, applySub [(x, t)] t2)) ts) ((x, t) : sub)
unifyTypes ((t, TVar x):ts) sub = unifyTypes ((TVar x, t) : ts) sub
unifyTypes ((TFun t11 t12, TFun t21 t22):ts) sub = unifyTypes ((t11, t21) : (t12, t22) : ts) sub
unifyTypes _ _ = Nothing


-- The following are tests cases to test your implementation

u1a, u1b, u2a, u2b, u3a, u3b :: Type
sub1, sub2, sub3 :: Maybe Sub

u1a = TFun (TVar "a") TInt
u1b = TVar "b"
sub1 = Just [("b",TFun (TVar "a") TInt)]
-- unifyTypes [(u1a,u1b)] [] should return sub1

u2a = TFun TBool TBool
u2b = TFun TBool TBool
sub2 = Just []
-- unifyTypes [(u2a,u2b)] [] should return sub2

u3a = TBool
u3b = TFun TInt TBool
sub3 = Nothing
-- unifyTypes [(u3a,u3b)] [] should return sub3

-- ADD MORE TESTS
-- ......
-- ......
------------------------------------------------------
---------------------- Task III: polymorphic type inference ----------------

-- Using unifyTypes, your task now is to define infer that does 
-- polymorphic type inference that can infer the type of an arbitrary expression 
-- written in mini Haskell that may include user-defined functions. 
-- You are allowed to use helper functions to implement infer. 
-- Use the names a1, a2, a3..., for the type variable names.

infer :: Expr -> TEnv -> Type
infer e tenv = case infer' e tenv [] 0 of
                 (ty, _) -> ty


infer' :: Expr -> TEnv -> Sub -> Int -> (Type, Int)
infer' (Number _) _ _ n = (TInt, n)
infer' (Boolean _) _ _ n = (TBool, n)
infer' (Id i) tenv _ _ = case lookup i tenv of
                           Just t -> (t, 0)
                           Nothing -> error $ "Unbound identifier: " ++ i
infer' (Prim p) tenv _ n = (lookupPrim p, n)


infer' (App e1 e2) tenv sub n =
  let (t1, n1) = infer' e1 tenv sub n
      (t2, n2) = infer' e2 tenv sub n1
      a = TVar $ "a" ++ show n2
      unifiedTypes = unifyTypes [(t1, TFun t2 a)] sub
  in case unifiedTypes of
       Just newSub -> (applySub newSub a, n2 + 1)
       Nothing -> error "Type mismatch in the App expression"
infer' (Cond e1 e2 e3) tenv sub n =
  let (t1, n1) = infer' e1 tenv sub n
      (t2, n2) = infer' e2 tenv sub n1
      (t3, n3) = infer' e3 tenv sub n2
      tBool = applySub sub TBool
      unifiedTypes = unifyTypes [(t1, tBool), (t2, t3)] sub
  in case unifiedTypes of
       Just newSub -> (applySub newSub t2, n3)
       Nothing -> error "Type mismatch in the Cond expression"
infer' (Fun i e) tenv sub n =
  let a = TVar $ "a" ++ show n
      b = TVar $ "b" ++ show (n + 1)
      tenv' = (i, a) : tenv
      (t, n2) = infer' e tenv' sub (n + 2)
  in (TFun a t, n2)

lookupPrim :: String -> Type
lookupPrim "+"  = TFun TInt (TFun TInt TInt)
lookupPrim "-"  = TFun TInt (TFun TInt TInt)
lookupPrim "*"  = TFun TInt (TFun TInt TInt)
lookupPrim "==" = TFun TInt (TFun TInt TBool)
lookupPrim "<=" = TFun TInt (TFun TInt TBool)
lookupPrim "&&" = TFun TBool (TFun TBool TBool)
lookupPrim "||" = TFun TBool (TFun TBool TBool)
lookupPrim "not" = TFun TBool TBool
lookupPrim _ = error "Unknown primitive"


  

-- The following are tests cases to test your implementation

ex4, ex5, ex6, ex7 :: Expr
type4, type5, type6, type7 :: Type

ex4 = Fun "x" (Boolean True)
type4 = TFun (TVar "a1") TBool
-- infer ex4 env should return type4

ex5 = Fun "x" (Id "x")
type5 = TFun (TVar "a1") (TVar "a1")
-- infer ex5 env should return type5

ex6 = Fun "x" (App (App (Prim "+") (Id "x")) (Number 1))
type6 = TFun TInt TInt
-- infer ex6 env should return type6

ex7 = Fun "x" (Fun "y" (App (Id "y") (Id "x")))
type7 = TFun (TVar "a1") (TFun (TFun (TVar "a1") (TVar "a3")) (TVar "a3"))
-- infer ex7 env should return type7



-- ADD MORE TESTS
-- ......
-- ......
------------------------------------------------------
main = do
  print (showT type1)
  print (showT type2)
  print (showT type3)
  print (showT type4)
  print (showT type5)
  print (showT type6)
  print (showT type7)