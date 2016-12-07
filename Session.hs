module Session where

import qualified Data.Set as S
import qualified Data.Map as M

data Name = Name String | CoName String
    deriving ( Show , Ord , Eq )

data Proc
    = Request Name  Name  Proc
    | Accept  Name  Name  Proc
    | Send    Name  Exp   Proc
    | Receive Name  Exp   Proc
    | Throw   Name  Name  Proc
    | Catch   Name  Name  Proc
    | Cond    Exp   Proc  Proc
    | Par     Proc  Proc
    | New     Name  Proc
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

sortExp :: Exp -> Maybe Sort
sortExp e = case e of
    BLit  b     -> Just SBool
    Conj  e1 e2 -> case (sortExp e1, sortExp e2) of
        (Just SBool, Just SBool) -> Just SBool
        _ -> Nothing
    Disj  e1 e2 -> case (sortExp e1, sortExp e2) of
        (Just SBool, Just SBool) -> Just SBool
        _ -> Nothing
    ALit  i     -> Just SNat
    Plus  e1 e2 -> case (sortExp e1, sortExp e2) of
        (Just SNat, Just SNat) -> Just SNat
        _ -> Nothing
    Minus e1 e2 -> case (sortExp e1, sortExp e2) of
        (Just SNat, Just SNat) -> Just SNat
        _ -> Nothing
    Var   n     -> undefined

data Type
    = TReceive [Sort] Type
    | TSend    [Sort] Type
    | TCatch   Name   Type
    | TThrow   Name   Type
    | TVar     Name
    | TQuant   Name   Type
    | TVoid
    | TBottom
    deriving ( Show , Ord , Eq )

type Typing = M.Map Name (Either Sort Type)

withoutTypingBinding :: Name -> Typing -> Typing
withoutTypingBinding = M.delete

type Env = (M.Map Name [Either Sort Type], M.Map Name (Either Sort Type))

lookupName :: Env -> Name -> Maybe (Either Sort Type)
lookupName env n = M.lookup n (snd env)

lookupProcVar :: Env -> Name -> [Either Sort Type]
lookupProcVar = (M.!) . fst

withoutEnvNameBinding :: Name -> Env -> Env
withoutEnvNameBinding n e = (fst e, M.delete n $ snd e)

coType :: Type -> Type
coType (TReceive ss t) = TSend    ss (coType t)
coType (TSend    ss t) = TReceive ss (coType t)
coType (TCatch   n  t) = TThrow   n  (coType t)
coType (TThrow   n  t) = TCatch   n  (coType t)
coType (TVar     n   ) = TVar     n
coType (TQuant   n  t) = TQuant   n  (coType t)
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

    Request a k  p -> do
        Left (SCoTypes t) <- lookupName env a
        typingP <- check (withoutEnvNameBinding a env) p
        Right t' <- M.lookup k typingP
        if t == coType t' then return $ withoutTypingBinding k typingP
        else Nothing

    Accept  a k  p -> do
        Left (SCoTypes t) <- lookupName env a
        typingP <- check (withoutEnvNameBinding a env) p
        Right t' <- M.lookup k typingP
        if t == t' then return $ withoutTypingBinding k typingP
        else Nothing

    Send    k e  p -> do
        sortE <- sortExp e
        Nothing
        
    Receive k x  p -> undefined
    Throw   k k' p -> undefined
    Catch   k k' p -> undefined
    Cond    e p  q -> undefined
    Par     p q    -> case (check env p, check env q) of
        (Just typingP, Just typingQ) | compatible typingP typingQ ->
            Just (composition typingP typingQ)
        _ -> Nothing
    New     n p   -> undefined
    Def     n a p -> undefined
    ProcVar n a   -> undefined
    End           -> undefined
