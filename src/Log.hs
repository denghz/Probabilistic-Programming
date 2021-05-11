{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Log where
import Continuation
-- import Control.Applicative
-- import Control.Monad
-- import Control.Monad.State

-- data LogState = LogOff | LogOn
--     deriving (Eq, Ord, Enum, Bounded, Show, Read)

-- newtype LogT m a = LogT { unLogT :: StateT LogState m a}
--     deriving (Functor, Monad, Applicative, MonadState LogState, MonadTrans, MonadIO)

-- runLog :: Monad m => LogT m a -> m a
-- runLog action = evalStateT (unLogT action) LogOn


-- loggingEnabled :: (Functor m, Monad m) => LogT m Bool
-- loggingEnabled = fmap (== LogOn) get

-- log' :: (Functor m, Monad m) => (l -> LogT m ()) -> l -> l -> m a -> LogT m a
-- log' logger before after action = do
--     doLog <- loggingEnabled
--     when doLog $ logger before
--     result <- lift action
--     when doLog $ logger after
--     return result

-- -- The function `log` already exists in Prelude as the logarithm, use a different name
-- log_ :: (Functor m, MonadIO m) => String -> String -> m a -> LogT m a
-- log_ = log' (liftIO . putStrLn)

-- enableLogging :: Monad m => LogT m ()
-- enableLogging = put LogOn

-- disableLogging :: Monad m => LogT m ()
-- disableLogging = put LogOff


-- testlog :: IO ()
-- testlog = runLog $ do
--     enableLogging
--     log_ "You'll see this" "Then this" $
--         putStrLn "First action"
--     disableLogging
--     log_ "But not this" "or this" $
--         putStrLn "Second action"

log_ :: String -> M a -> M a
log_ l m =
    do
      m' <- m 
      Mk (\k ->
          do 
            putStr l
            k m')