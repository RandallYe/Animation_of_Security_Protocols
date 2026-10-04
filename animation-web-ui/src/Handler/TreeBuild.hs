{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Preload the protocol event trees.
--
--   The trees are built from the Isabelle-proved bounded exploration, which can
--   take minutes for the larger models.  Building them in a forked thread at
--   startup keeps that cost out of the request path; a request that still finds
--   a table empty waits on the same per-protocol lock instead of building a
--   second tree.
module Handler.TreeBuild (preloadEventTrees) where

import Import
import qualified Handler.AnimateNSPK3  as NSPK3
import qualified Handler.AnimateNSLPK3 as NSLPK3
import qualified Handler.AnimateNSWJ3  as NSWJ3
import qualified Handler.AnimateDHWJ   as DHWJ
import qualified NSWJ3_config as NSWJ3Config
import qualified DHWJ_config  as DHWJConfig

-- | Build every protocol event tree that is not in the database yet.
preloadEventTrees :: Handler ()
preloadEventTrees = do
    liftIO $ putStrLn "preloadEventTrees: building missing protocol event trees"
    NSPK3.ensureEventTree
    NSLPK3.ensureEventTree
    mapM_ NSWJ3.ensureEventTree [NSWJ3Config.Eve1, NSWJ3Config.Eve2,
                                 NSWJ3Config.Eve3, NSWJ3Config.Eve4]
    mapM_ DHWJ.ensureEventTree  [DHWJConfig.Eve1, DHWJConfig.Eve2,
                                 DHWJConfig.Eve3, DHWJConfig.Eve4]
    liftIO $ putStrLn "preloadEventTrees: done"
