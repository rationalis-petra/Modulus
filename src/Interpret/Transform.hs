module Interpret.Transform where

import Data


instance (Functor m) => Functor (ActionMonadT m) where
  fmap f (ActionMonadT outer_monad) =
    let inner_func (RaiseAction cnt id1 id2 args def) =
          RaiseAction (\arg -> fmap f (cnt arg)) id1 id2 args def
        inner_func (Value x) =
          Value (f x)
    in ActionMonadT $ fmap inner_func outer_monad
      

instance (Applicative m) => Applicative (ActionMonadT m) where
  (ActionMonadT func_mnd) <*> (ActionMonadT val_mnd) =
    let inner_app (RaiseAction cnt id1 id2 args def) mv =
          RaiseAction (\arg -> (cnt arg) <*> (ActionMonadT $ pure mv)) id1 id2 args def
        inner_app (Value func) mv =
          case mv of
            RaiseAction cnt id1 id2 args def ->
              RaiseAction (\arg ->
                             (ActionMonadT $ pure (Value func)) <*> (cnt arg)) id1 id2 args def
            Value val -> 
              Value $ func val

    in ActionMonadT $ inner_app <$> func_mnd <*> val_mnd 
    
  pure x = ActionMonadT $ pure $ Value x


instance (Monad m) => Monad (ActionMonadT m) where
  (ActionMonadT mnd) >>= f = 
    let inner_f (RaiseAction cnt id1 id2 args def) =
          pure $ RaiseAction (\arg -> (cnt arg) >>= f) id1 id2 args def
        inner_f (Value val) =
          let (ActionMonadT mnd) = f val in mnd
    in ActionMonadT $ mnd >>= inner_f
  

lift :: (Monad m) => m a -> ActionMonadT m a
lift m = ActionMonadT (m >>= \x -> pure $ Value x)

-- raise :: (Monad m) => String -> [Object m] -> (ActionMonadT m (Object (ActionMonadT m)))
raise id1 id2 args def = 
  ActionMonadT $ pure $ RaiseAction pure id1 id2 args def
  

instance Show a => Show (MaybeEffect m a) where
  show m = case m of
    RaiseAction _ id1 id2 args _ ->
      foldr (<>) "(RaisedAction " [show id1, ",", show id2, "with args: ", show args, ")"]
    Value x -> "(Value " ++ show x ++ ")"

