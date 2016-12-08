module Session where

{- Here we implement the type system described in the paper. We make three main
 - simplifications to ease the implementation burden:
 -     1: Input & output communication is monadic - this frees us from the
 -        burden of dealing with lists of types and expressions. It's easier to
 -        handle just one.
 -     2: We do not include branch/select operations - It's straightforward to
 -        understand but creates a lot of implementation work.
 -     3: Inputs are labelled with a type - frees us from having to do a
 -        constraint generation and unification. We can check a process in a
 -        single pass.
 -}

import qualified Data.Set as S
import qualified Data.Map as M

data Name = Name String | CoName String
    deriving ( Show , Ord , Eq )

data Proc
    = Request Name  Name  Proc
    | Accept  Name  Name  Proc
    | Send    Name  Exp   Proc
    | Receive Name  Name  Sort Proc
    | Throw   Name  Name  Proc
    | Catch   Name  Name  Proc
    | Cond    Exp   Proc  Proc
    | Par     Proc  Proc
    | New     Name  EST   Proc
    | Def     Name [Name] Proc
    | ProcVar Name [Exp ]
    | End
    deriving ( Show , Ord , Eq )

data Exp
    = BLit  Bool
    | Conj  Exp Exp
    | Disj  Exp Exp
    | ALit  Int
    | Plus  Exp Exp
    | Minus Exp Exp
    | Var   Name
    deriving ( Show , Ord , Eq )

data Sort = SNat | SBool | SCoTypes Type | SVar Name | SQuant Name Sort
    deriving ( Show , Ord , Eq )

sortExp :: Env -> Exp -> Maybe Sort
sortExp env exp = case exp of
    BLit  b     -> Just SBool
    Conj  e1 e2 -> case (sortExp env e1, sortExp env e2) of
        (Just SBool, Just SBool) -> Just SBool
        _ -> Nothing
    Disj  e1 e2 -> case (sortExp env e1, sortExp env e2) of
        (Just SBool, Just SBool) -> Just SBool
        _ -> Nothing
    ALit  i     -> Just SNat
    Plus  e1 e2 -> case (sortExp env e1, sortExp env e2) of
        (Just SNat, Just SNat) -> Just SNat
        _ -> Nothing
    Minus e1 e2 -> case (sortExp env e1, sortExp env e2) of
        (Just SNat, Just SNat) -> Just SNat
        _ -> Nothing
    Var   n     -> do
        Left sort <- lookupName env n
        return sort

data Type
    = TReceive Sort Type
    | TSend    Sort Type
    | TCatch   Type Type
    | TThrow   Type Type
    | TVar     Name
    | TQuant   Name Type
    | TVoid
    | TBottom
    deriving ( Show , Ord , Eq )

type EST = Either Sort Type

type Typing = M.Map Name EST

withoutTypingBinding :: Name -> Typing -> Typing
withoutTypingBinding = M.delete

type Env = (M.Map Name [EST], M.Map Name EST)

lookupName :: Env -> Name -> Maybe EST
lookupName env n = M.lookup n (snd env)

lookupProcVar :: Env -> Name -> [EST]
lookupProcVar = (M.!) . fst

withoutEnvNameBinding :: Name -> Env -> Env
withoutEnvNameBinding n e = (fst e, M.delete n $ snd e)

withEnvNameBinding :: Name -> EST -> Env -> Env
withEnvNameBinding n t e = (fst e, M.insert n t $ snd e)

coType :: Type -> Type
coType (TReceive s t) = TSend    s (coType t)
coType (TSend    s t) = TReceive s (coType t)
coType (TCatch   k t) = TThrow   k (coType t)
coType (TThrow   k t) = TCatch   k (coType t)
coType (TVar     n  ) = TVar     n
coType (TQuant   n t) = TQuant   n (coType t)
coType  TVoid          = TVoid
coType  TBottom        = error "TBottom has no coType"

compatible :: Typing -> Typing -> Bool
compatible t1 t2 = and
    $ map (\k -> (t1 M.! k) == (t2 M.! k))
    $ S.toList
    $ S.intersection (M.keysSet t1) (M.keysSet t2)

composition :: Typing -> Typing -> Typing
composition t1 t2
    | compatible t1 t2 = M.unionWith (\_ _ -> Right TBottom) t1 t2
    | otherwise        = undefined

check :: Env -> Proc -> Maybe Typing
check env proc = case proc of

    Request a k p -> do
        Left (SCoTypes t) <- lookupName env a
        typingP <- check (withoutEnvNameBinding a env) p
        Right tyKInP <- M.lookup k typingP
        if t == coType tyKInP then return $ withoutTypingBinding k typingP
        else Nothing

    Accept a k p -> do
        Left (SCoTypes t) <- lookupName env a
        typingP <- check (withoutEnvNameBinding a env) p
        Right tyKInP <- M.lookup k typingP
        if t == tyKInP then return $ withoutTypingBinding k typingP
        else Nothing

    Send k e p -> do
        sortE <- sortExp env e
        typingP <- check env p
        Right tyKInP <- M.lookup k typingP
        return $ M.insert k (Right (TSend sortE tyKInP)) typingP
        
    Receive k x s p -> do
        typingP <- check (withEnvNameBinding x (Left s) env) p
        Right tyKInP <- M.lookup k typingP
        return $ M.insert k (Right (TReceive s tyKInP)) typingP

    Throw k k' p -> do
        Right tyK' <- lookupName env k'
        typingP <- check env p
        Right tyKInP <- M.lookup k typingP
        return $ M.insert k (Right (TThrow tyK' tyKInP)) typingP

    Catch k k' p -> do
        typingP <- check env p
        Right tyKInP <- M.lookup k typingP
        Right tyK'InP <- M.lookup k' typingP
        return
            $ M.insert k (Right (TCatch tyK'InP tyKInP))
            $ withoutTypingBinding k' typingP

    Cond e p q -> do
        sortE <- sortExp env e
        typingP <- check env p
        typingQ <- check env q
        if typingP == typingQ && sortE == SBool then
            return $ composition typingP typingQ
        else Nothing

    Par p q -> do
        typingP <- check env p
        typingQ <- check env q
        if compatible typingP typingQ then return $ composition typingP typingQ
        else Nothing

    New a (Left s) p -> check (withEnvNameBinding a (Left s) env) p

    New k (Right t) p -> do
        typingP <- check env p
        Right tyKInP <- M.lookup k typingP
        if tyKInP == TBottom then return $ withoutTypingBinding k typingP
        else Nothing

    Def     n a p -> undefined
    ProcVar n a   -> undefined
    End           -> undefined
