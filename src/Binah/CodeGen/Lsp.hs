{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Binah.CodeGen.Lsp
    ( run
    )
where

import           Control.Concurrent
import           Control.Concurrent.STM.TChan
import qualified Control.Exception             as E
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.STM
import           Data.Default
import qualified Data.HashMap.Strict           as H
import qualified Data.Text                     as T
import qualified Language.Haskell.LSP.Control  as CTRL
import qualified Language.Haskell.LSP.Core     as Core
import           Language.Haskell.LSP.Diagnostics
import           Language.Haskell.LSP.Messages
import qualified Language.Haskell.LSP.Types    as J
import qualified Language.Haskell.LSP.Types.Lens
                                               as J
import qualified Language.Haskell.LSP.Utility  as U
import           Language.Haskell.LSP.VFS
import           System.Exit
import qualified System.Log.Logger             as L

import           Binah.CodeGen.Check
import           Binah.CodeGen.Parser           ( parse )
import           Binah.CodeGen.UX


-- ---------------------------------------------------------------------

run :: IO () -> IO Int
run dispatcherProc = flip E.catches handlers $ do

    rin <- atomically newTChan :: IO (TChan ReactorInput)

    let dp lf = do
            _rpid <- forkIO $ reactor lf rin
            dispatcherProc
            return Nothing

        callbacks = Core.InitializeCallbacks { Core.onInitialConfiguration = const $ Right ()
                                             , Core.onConfigurationChange  = const $ Right ()
                                             , Core.onStartup              = dp
                                             }

    flip E.finally finalProc $ CTRL.run callbacks (lspHandlers rin) lspOptions Nothing

  where
    handlers  = [E.Handler ioExcept, E.Handler someExcept]
    finalProc = L.removeAllHandlers
    ioExcept (e :: E.IOException) = print e >> return 1
    someExcept (e :: E.SomeException) = print e >> return 1

-- ---------------------------------------------------------------------

newtype ReactorInput = HandlerRequest FromClientMessage

-- ---------------------------------------------------------------------

-- | The monad used in the reactor
type R c a = ReaderT (Core.LspFuncs c) IO a

-- ---------------------------------------------------------------------

publishDiagnostics
    :: Int -> J.NormalizedUri -> J.TextDocumentVersion -> DiagnosticsBySource -> R () ()
publishDiagnostics maxToPublish uri v diags = do
    lf <- ask
    liftIO $ Core.publishDiagnosticsFunc lf maxToPublish uri v diags

-- ---------------------------------------------------------------------

reactor :: Core.LspFuncs () -> TChan ReactorInput -> IO ()
reactor lf inp = do
    liftIO $ U.logs "reactor:entered"
    flip runReaderT lf $ forever $ do
        inval <- liftIO $ atomically $ readTChan inp
        case inval of
            HandlerRequest (NotDidChangeTextDocument notification) -> do
                let doc = notification ^. J.params . J.textDocument
                checkFile doc

            HandlerRequest om -> return ()

checkFile :: J.VersionedTextDocumentIdentifier -> R () ()
checkFile doc = do
    lf   <- ask
    mdoc <- liftIO $ Core.getVirtualFileFunc lf normalizedUri
    let errors = maybe [] parseAndCheck mdoc
    let diags  = map diagnosticFromError errors
    liftIO $ U.logs $ "sending diagnostics" ++ show (length diags)
    publishDiagnostics 100 normalizedUri version (partitionBySource diags)
  where
    normalizedUri = doc ^. J.uri . to J.toNormalizedUri
    version       = doc ^. J.version

parseAndCheck :: VirtualFile -> [UserError]
parseAndCheck file = case parse "FILE" text of
    Left  e     -> mkParseErrors e
    Right binah -> checkBinah binah
    where text = virtualFileText file

diagnosticFromError :: UserError -> J.Diagnostic
diagnosticFromError (Error s ss) = J.Diagnostic (sourceSpanToRange ss)
                                                (Just J.DsError)
                                                Nothing
                                                (Just "binah-lsp")
                                                (T.pack s)
                                                (Just (J.List []))

sourceSpanToRange :: SourceSpan -> J.Range
sourceSpanToRange (SS begin end) = J.Range (f begin) (f end)
    where f (SourcePos _ line column) = J.Position (unPos line - 1) (unPos column - 1)

-- ---------------------------------------------------------------------

syncOptions :: J.TextDocumentSyncOptions
syncOptions = J.TextDocumentSyncOptions { J._openClose         = Just True
                                        , J._change            = Just J.TdSyncIncremental
                                        , J._willSave          = Just False
                                        , J._willSaveWaitUntil = Just False
                                        , J._save              = Just $ J.SaveOptions $ Just False
                                        }

lspOptions :: Core.Options
lspOptions = def { Core.textDocumentSync = Just syncOptions }

lspHandlers :: TChan ReactorInput -> Core.Handlers
lspHandlers rin = def
    { Core.didChangeTextDocumentNotificationHandler = Just
                                                          $ passHandler rin NotDidChangeTextDocument
    }

-- ---------------------------------------------------------------------

passHandler :: TChan ReactorInput -> (a -> FromClientMessage) -> Core.Handler a
passHandler rin c notification = atomically $ writeTChan rin (HandlerRequest (c notification))
