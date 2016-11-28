module LinearPi where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (intersperse)
import Data.Maybe (catMaybes)
import Control.Monad (liftM, ap)
import System.Exit

--------------------------------------------------------------------------------
-- Error monad for this implementation
--------------------------------------------------------------------------------

data Result a = Error String | NoError a

instance Functor Result where
    fmap = liftM

instance Applicative Result where
    pure  = return
    (<*>) = ap

instance Monad Result where
    (>>=) (Error   s) f = Error s
    (>>=) (NoError r) f = f r
    return = NoError

fromResult :: Result a -> a
fromResult (NoError a) = a
fromResult (Error   e) = error e

--------------------------------------------------------------------------------
-- Term definitions
--------------------------------------------------------------------------------

type Name = Int

showName :: Name -> String
showName n = case n of { 0 -> "x" ; 1 -> "y" ; 2 -> "z" ;
                       ; 3 -> "a" ; 4 -> "b" ; 5 -> "c" ; _ -> "n" ++ show n }

data Term
    = Parallel Term Term
    | Output Name [Expression]
    -- In this implementation, input bindings have type labels. This allows us
    -- to typecheck fully compositionally, avoiding separate constraint
    -- generation and unification phases.
    | Input Bool Name [(Name, Type)] Term
    | New Name Type Term
    | If Expression Term Term
    deriving (Eq, Ord)

instance Show Term where
    show (Parallel p1 p2)  = show p1 ++ " | " ++ show p2
    show (Output n es)     = showName n ++ "!" ++ show es
    show (Input r n ets p) = showName n ++ "?" ++ (if r then "*" else "")
        ++ "[" ++ concat (intersperse ", " (map (\(n, t) -> showName n
        ++ ": " ++ show t) ets)) ++ "]." ++ show p
    show (New n t p)       =
        "(new " ++ showName n ++ ": " ++ show t ++ ")" ++ show p
    show (If e p1 p2)      =
        "if " ++ show e ++ " then " ++ show p1 ++ " else " ++ show p2

data Expression = Variable Name | Literal Bool
    deriving (Eq, Ord)

instance Show Expression where
    show (Literal True ) = "true"
    show (Literal False) = "false"
    show (Variable n   ) = showName n

--------------------------------------------------------------------------------
-- Type definitions
--------------------------------------------------------------------------------

data Type = Boolean | Channel Polarity Multiplicity [Type]
    deriving (Eq, Ord)

instance Show Type where
    show Boolean = "bool"
    show (Channel pol mul ts) = showPol pol ++ show mul ++ show ts

type Polarity = S.Set Direction

data Direction = In | Out
    deriving (Eq, Ord)

instance Show Direction where
    show In = "input"
    show Out = "output"

data Multiplicity = Lin | Unlim
    deriving (Eq, Ord)

instance Show Multiplicity where
    show Lin   = "1"
    show Unlim = "+"

input  :: Polarity
input  = S.singleton In
output :: Polarity
output = S.singleton Out
inout  :: Polarity
inout  = S.fromList [In, Out]
dead   :: Polarity
dead   = S.empty

polarity :: Type -> Result Polarity
polarity (Channel p _ _) = return p
polarity Boolean         = Error "polarity: booleans have no polarity"

showPol :: Polarity -> String
showPol p
    | p == input  = "input"
    | p == output = "output"
    | p == inout  = "inout"
    | p == dead   = "dead"

combine :: Type -> Type -> Result Type
combine Boolean Boolean = return Boolean
combine (Channel p1 Unlim ts1) (Channel p2 Unlim ts2) | ts1 == ts2 =
    return $ Channel (p1 `S.union` p2) Unlim ts1
combine (Channel p1 Lin   ts1) (Channel p2 Lin   ts2) | ts1 == ts2
    && S.intersection p1 p2 == S.empty =
        return $ Channel (p1 `S.union` p2) Lin ts1
combine t1 t2 = Error $
    "combine: incompatible types: " ++ show t1 ++ ", " ++ show t2

-- Combine two types, but without knowing the multiplicity of the second,
-- defaulting to the multiplicity from the first.
combinePartial :: Type -> (Polarity, [Type]) -> Result Type
combinePartial t1@(Channel _ m _) (p, ts) = combine t1 (Channel p m ts)

diff :: Type -> Type -> Result Type
diff Boolean Boolean = return Boolean
diff (Channel p1 Unlim ts1) (Channel p2 Unlim ts2) | ts1 == ts2 &&
    p2 `S.isSubsetOf` p1 =
        return $ Channel p1 Unlim ts1
diff (Channel p1 Lin ts1  ) (Channel p2 Lin ts2  ) | ts1 == ts2 &&
    p2 `S.isSubsetOf` p1 =
        return $ Channel (S.filter (\e -> S.notMember e p2) p1) Lin ts1
diff t1 t2 = Error $
    "diff: incompatible types: " ++ show t1 ++ ", " ++ show t2

--------------------------------------------------------------------------------
-- Type environment definitions
--------------------------------------------------------------------------------

type Env = M.Map Name Type

showEnv :: Env -> String
showEnv = concat . intersperse ", "
    . map (\(n,t) -> show n ++ ": " ++ show t). M.toList

envLookup :: Env -> Name -> Result Type
envLookup env n = case M.lookup n env of
    Just  t -> return t
    Nothing -> Error "lookupEnv: variable not found in environment"

envInsert :: Name -> Type -> Env -> Env
envInsert = M.insert

envInsertMany :: [(Name, Type)] -> Env -> Result Env
envInsertMany nts env
    | length nts == S.size (S.fromList (map fst nts)) = return $
        M.unions ((map (uncurry M.singleton) nts) ++ [env])
    | otherwise = Error "envInsertMany: Bound matching names simultaneously"

-- The supplied type is given as the right-hand argument to the supplied
-- function. The function argument and insertion parameter have a generic type
-- so that envCombinePartial can use envInsertWith with combinePartial when
-- multiplicities are not known.
envInsertWith :: (Type -> a -> Result Type) ->
    Name -> a -> Env -> Result Env
envInsertWith f n tNew env = do
    tOld      <- envLookup env n
    tCombined <- f tOld tNew
    return $ M.insert n tCombined env

envCombine :: Name -> Type -> Env -> Result Env
envCombine = envInsertWith combine

envCombineAll :: [(Name, Type)] -> Env -> Result Env
envCombineAll []           env = return env
envCombineAll ((n, t):nts) env = do
    env' <- envCombine n t env
    envCombineAll nts env'

envCombinePartial :: Name -> (Polarity, [Type]) -> Env -> Result Env
envCombinePartial = envInsertWith combinePartial

envDiff :: Name -> Type -> Env -> Result Env
envDiff = envInsertWith diff

unlimited :: Env -> Bool
unlimited = all $ \t -> case t of
    Channel _ Unlim _             -> True
    Channel p _     _ | p == dead -> True
    Boolean                       -> True
    _                             -> False

assertUnlimited :: Env -> Result ()
assertUnlimited env | unlimited env = return ()
assertUnlimited env | otherwise     = Error "assertUnlimited: assertion failed"

envUnion :: Env -> Env -> Result Env
envUnion e1 e2 | M.keysSet e1 == M.keysSet e2 =
    let keys       = map fst (M.assocs e1)
        values1    = map snd (M.assocs e1)
        values2    = map snd (M.assocs e2)
        valuePairs = zip values1 values2
        combined   = sequence $ map (uncurry combine) valuePairs
        newKVPairs = fmap (zip keys) combined
        newMap     = fmap M.fromList newKVPairs
    in newMap
envUnion _  _  | otherwise                    =
    Error "envUnion: union of incompatible environments"

-- Assert that a given name has a given capability in the given environment
capabilityAssert :: Env -> Name -> Direction -> Result ()
capabilityAssert env n dir = do
    ty <- envLookup env n
    case ty of
        Channel pol _ _ | S.member dir pol -> return ()
        t -> Error $ "capabilityAssert: assertion failed - " ++ show n ++
            ": " ++ show t ++ " - asserted " ++ show dir ++ " capability"

-- Split a polarity for left and right side parallel composition
polSplits :: Polarity -> [(Polarity, Polarity)]
polSplits p | p == input  =
                [ (input , dead  )
                , (dead  , input )
                ]
           | p == output =
                [ (output, dead  )
                , (dead  , output)
                ]
           | p == dead   =
                [ (dead  , dead  )
                ]
           | p == inout  =
                [ (input , output)
                , (output, input )
                , (inout , dead  )
                , (dead  , inout )
                ]

-- Split a type for left and right side parallel composition
tySplits :: Type -> [(Type, Type)]
tySplits t@Boolean                = [(t, t)]
tySplits t@(Channel _   Unlim _ ) = [(t, t)]
tySplits t@(Channel pol Lin   ts) =
    map (\(p1, p2) -> (Channel p1 Lin ts, Channel p2 Lin ts)) (polSplits pol)

envSplits :: Env -> S.Set (Env, Env)
envSplits env = case M.toList env of
    []            -> S.empty
    [(x, t)]      -> S.fromList $
        map (\(t1, t2) -> (M.singleton x t1, M.singleton x t2)) (tySplits t)
    (x, t) : env' -> S.fromList $ concat $ map (\(e1, e2) -> map (\(t1, t2) ->
        (M.insert x t1 e1, M.insert x t2 e2)) (tySplits t))
        (S.toList (envSplits (M.fromList env')))

--------------------------------------------------------------------------------
-- Type checker functions
--------------------------------------------------------------------------------

dropLits :: [(Expression, Type)] -> [(Name, Type)]
dropLits []            = []
dropLits ((e, t): ets) = case e of
    Literal  _ -> dropLits ets
    Variable n -> (n, t) : dropLits ets

checkExp :: Env -> Expression -> Result Type
checkExp _   (Literal  _) = return Boolean
checkExp env (Variable n) = envLookup env n

check :: Env -> Term -> Result Env
check env t = case t of

    Parallel p q -> let
        splitresults = map (\(e1, e2) -> (check e1 p, check e2 q))
            $ S.toList $ envSplits env
        in
        case catMaybes $ map ( \p -> case p of
            { (NoError e1', NoError e2') -> Just (e1', e2')
            ; _ -> Nothing
            } ) splitresults of
                (e1', e2'):_ -> envUnion e1' e2'
                [] ->
                    Error $ "check: No successful splits in Parallel for process "
                        ++ show t ++ ", with environment " ++ showEnv env

    Output n es -> do
        assertUnlimited $ M.delete n env
        capabilityAssert env n Out
        tes   <- sequence $ map (checkExp env) es
        env'  <- envCombinePartial n (output, tes) env
        env'' <- envCombineAll (dropLits (zip es tes)) env'
        return env''

    Input False n nts p -> do
        env' <- envInsertMany nts env
        check env' p
        envCombinePartial n (input, map snd nts) env

    Input True n nts p -> do
        env' <- envInsertMany nts env
        check env' p
        if unlimited env then
            envCombine n (Channel input Unlim (map snd nts)) env
        else
            Error "check: Replication with limited environment"

    New n ty p -> do
        let env' = envInsert n ty env
        check env' p
        polarityTy <- polarity ty
        if polarityTy == inout || polarityTy == dead then
            return env
        else
            Error "check: Declared channel not inout or dead"

    If e p q -> do
        check env p
        check env q
        tE <- checkExp env e
        if tE == Boolean then do
            env' <- envCombineAll (dropLits [(e, tE)]) env
            return env'
        else do
            Error "check: if-guard was not boolean"


--------------------------------------------------------------------------------
-- A main function with some tests
--------------------------------------------------------------------------------

main :: IO ExitCode
main = let result = check M.empty p in case result of
    Error   s -> do
        putStrLn $ "Test failed - " ++ s
        putStrLn $ "Original program: " ++ show p
        exitFailure
    NoError _ -> do
        putStrLn "Test passed."
        exitSuccess

p :: Term
p = New 0 (Channel inout Lin [Boolean])
        (New 1 (Channel inout Lin [Boolean])
            (Parallel
                (Parallel
                    (Output 0 [Literal True ])
                    (Output 1 [Literal False])
                )
                (Input False 0 [(2, Boolean)]
                    (Input False 1 [(3, Boolean)]
                        (New 4 (Channel dead Unlim [Boolean])
                            (Output 4 [Literal True])
                        )
                    )
                )
            )
        )
