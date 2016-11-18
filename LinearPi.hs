module LinearPi where

import qualified Data.Set as S
import qualified Data.Map as M
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

--------------------------------------------------------------------------------
-- Term definitions
--------------------------------------------------------------------------------

type Name = Int

data Term
    = Parallel Term Term
    | Output Name [Expression]
    -- In this implementation, input bindings have type labels. This allows us
    -- to typecheck fully compositionally, avoiding separate constraint
    -- generation and unification phases.
    | Input Bool Name [(Name, Type)] Term
    | New Name Type Term
    | If Expression Term Term
    deriving (Show, Eq, Ord)

data Expression = Variable Name | Literal Bool
    deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- Type definitions
--------------------------------------------------------------------------------

data Type = Boolean | Channel Polarity Multiplicity [Type]
    deriving (Show, Eq, Ord)

type Polarity = S.Set Direction

data Direction = In | Out
    deriving (Show, Eq, Ord)

data Multiplicity = One | Unlim
    deriving (Show, Eq, Ord)

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

combine :: Type -> Type -> Result Type
combine Boolean Boolean = return Boolean
combine (Channel p1 Unlim ts1) (Channel p2 Unlim ts2) | ts1 == ts2 =
    return $ Channel (p1 `S.union` p2) Unlim ts1
combine (Channel p1 One   ts1) (Channel p2 One   ts2) | ts1 == ts2
    && S.intersection p1 p2 == S.empty =
        return $ Channel (p1 `S.union` p2) One ts1
combine _ _ = Error "combine: incompatible types"

-- Combine two types, but without knowing the multiplicity of the second,
-- defaulting to the multiplicity from the first.
combinePartial :: Type -> (Polarity, [Type]) -> Result Type
combinePartial t1@(Channel _ m _) (p, ts) = combine t1 (Channel p m ts)

diff :: Type -> Type -> Result Type
diff Boolean Boolean = return Boolean
diff (Channel p1 Unlim ts1) (Channel p2 Unlim ts2) | ts1 == ts2 &&
    p2 `S.isSubsetOf` p1 =
        return $ Channel p1 Unlim ts1
diff (Channel p1 One ts1  ) (Channel p2 One ts2  ) | ts1 == ts2 &&
    p2 `S.isSubsetOf` p1 =
        return $ Channel (S.filter (\e -> S.notMember e p2) p1) One ts1
diff _ _ = Error "diff: incompatible types"

--------------------------------------------------------------------------------
-- Type environment definitions
--------------------------------------------------------------------------------

type Env = M.Map Name Type

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
unlimited = null . filter (not . unlimOrDead) . map snd . M.toList where
    unlimOrDead :: Type -> Bool
    unlimOrDead t = case t of
        Channel _ Unlim _                -> True
        Channel p _     _ | p == S.empty -> True
        _                                -> False

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

    Parallel p q -> do
        env'  <- check env  p
        env'' <- check env' q
        envUnion env' env''

    Output n es | unlimited env -> do
        tes   <- sequence $ map (checkExp env) es
        env'  <- envCombinePartial n (output, tes) env
        env'' <- envCombineAll (dropLits (zip es tes)) env'
        return env''
    Output _ _  | otherwise -> Error "check: Output with limited environment"

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
        exitFailure
    NoError _ -> do
        putStrLn "Test passed."
        exitSuccess

p :: Term
p = New 0 (Channel inout One [Boolean])
        (New 1 (Channel inout One [Boolean])
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
