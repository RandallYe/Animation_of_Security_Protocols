{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}

-- | Common handler functions.
module Handler.Common where

import Data.FileEmbed (embedFile)
import Yesod.Form.Bootstrap3 -- (BootstrapFormLayout (..), renderBootstrap3, BootstrapGridOptions(..), bootstrapSubmit, BootstrapSubmit) 
import Import
import Network.HTTP.Simple
import Data.Text           as T
import Data.Text.Encoding  as T
import Data.Text.IO        as T
import qualified Data.List as DL (dropWhile, dropWhileEnd, intersect, head, tail, elemIndex, uncons, splitAt);
import qualified Data.Map as M
import Data.ByteString.UTF8 as B
import Data.ByteString.Lazy.UTF8 as LB
import Text.Blaze.Internal as TBI
import "nspk3-animator" Simulate as NSPK3_Simulate
import NSPK3_Animate (explore_tree_NSPK3, 
  explore_tree_NSLPK3, EventTree(ETNode), TEventPos(TEP), TEvent(Root, Deadlocked, Terminated, Divergent, EChan),
  )

-- These handlers embed files in the executable at compile time to avoid a
-- runtime dependency, and for efficiency.

getFaviconR :: Handler TypedContent
getFaviconR = do cacheSeconds $ 60 * 60 * 24 * 30 -- cache for a month
                 return $ TypedContent "image/x-icon"
                        $ toContent $(embedFile "config/favicon.ico")

getRobotsR :: Handler TypedContent
getRobotsR = return $ TypedContent typePlain
                    $ toContent $(embedFile "config/robots.txt")

data CheckMode = Secrecy | Correspondence
  deriving (Eq, Show)

fst4 :: (a, b, c, d) -> a
fst4 (a, _, _, _) = a

snd4 :: (a, b, c, d) -> b
snd4 (_, b, _, _) = b

thd4 :: (a, b, c, d) -> c
thd4 (_, _, c, _) = c

fth4 :: (a, b, c, d) -> d
fth4 (_, _, _, d) = d 

fst5 :: (a, b, c, d, e) -> a
fst5 (a, _, _, _, _) = a

snd5 :: (a, b, c, d, e) -> b
snd5 (_, b, _, _, _) = b

thd5 :: (a, b, c, d, e) -> c
thd5 (_, _, c, _, _) = c

fth5 :: (a, b, c, d, e) -> d
fth5 (_, _, _, d, _) = d

fifth5 :: (a, b, c, d, e) -> e
fifth5 (_, _, _, _, e) = e

getPlantUMLDiagram :: Text -> Handler TBI.Markup 
getPlantUMLDiagram plantUmlCode = do 
    -- Define PlantUML diagram text
    -- let plantUmlCode = T.unlines
    --         [ "@startuml"
    --         , "Alice -> Bob: Hello"
    --         , "Bob --> Alice: Hi"
    --         , "@enduml"
    --         ]
    
    -- Define PlantUML server endpoint (use localhost or public server)
    -- let url = "http://localhost:8080/plantuml/svg"
    url <- T.unpack <$> getPlantUMLURL 

    -- Create a POST request with the diagram as body
    let request = setRequestBodyLBS (LB.fromString $ T.unpack plantUmlCode) $
                  setRequestMethod "POST" $
                  parseRequest_ url

    -- Send the request and get the response
    response <- httpBS request

    -- Save the response body (the generated SVG) to a file
    return $ preEscapedToMarkup $ B.toString $ getResponseBody response

getPlantUMLURL :: Handler Text 
getPlantUMLURL = do 
    -- Get the foundation (App)
    app <- getYesod

    -- Access appSettings from the foundation
    let settings = appSettings app

    -- Extract specific settings, e.g., appTitle
    return $ appPlantUmlUrl settings

{-
  plantUMLHeader ++ [
  "Env -> Alice: Intruder", 
  "Alice -> Alice: ClaimSecret (N Alice) {Intruder}", 
  "Alice -> Intruder: {<N Alice, Alice>}_{PK Intruder}", 
  "Intruder -> Bob: {<N Alice, Alice>}_{PK Bob}", 
  "Bob -> Bob: ClaimSecret (N Bob) {Alice}", 
  "Bob -> Bob: StartProt Bob Alice (N Alice) (N Bob) ", 
  "Bob -> Intruder: {<N Alice, N Bob>}_{PK Alice}", 
  "Intruder -> Alice: {<N Alice, N Bob>}_{PK Alice}", 
  "Alice -> Alice: StartProt Alice Intruder (N Alice) (N Bob)", 
  "Alice -> Intruder: {<N Bob>}_{PK Intruder}", 
  "Intruder -[#red]> Intruder: Leak (N Bob) ", 
  "@enduml"
  ]
-}

formatPlantUMLInput :: (Text, Text, Text) -> Text
formatPlantUMLInput (src, dst, ch_msg) = 
  src <> " -> " <> dst <> ": " <> ch_msg

plantUMLHeader :: [Text]
plantUMLHeader = [
  "@startuml",
  "autonumber \"[00]\"",
  "entity Env",
  "boundary Sys #green",
  "box \"Protocol\" #Snow", 
  "actor Alice #blue",
  "participant Intruder #yellow",
  "actor Bob #red",
  "end box"
  ] 

plantUMLTail :: [Text]
plantUMLTail = [ "@enduml" ] 

plantUMLInput4Animation :: Handler Text
plantUMLInput4Animation = do
  maybeNext <- lookupSession "plantuml_input"
  case maybeNext of
    Nothing -> return $ T.unlines $ 
      plantUMLHeader ++ plantUMLTail
    Just str_trace -> return $ T.unlines $ 
      plantUMLHeader ++ [str_trace] ++ plantUMLTail

plantUMLInput4Counterexample :: Handler Text
plantUMLInput4Counterexample = do
  maybeNext <- lookupSession sessionCntExPlantumlInputKey
  case maybeNext of
    Nothing -> return $ T.unlines $ 
      plantUMLHeader ++ plantUMLTail
    Just str_trace -> return $ T.unlines $ 
      plantUMLHeader ++ [str_trace] ++ plantUMLTail

plantUMLTextEmpty :: Handler Text
plantUMLTextEmpty = return $ T.unlines $ 
      plantUMLHeader ++ plantUMLTail

plantUMLTextNSPK7 :: Handler Text
plantUMLTextNSPK7 = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "database Server #green",
  "actor Bob #red",
  "Alice -> Server : (Alice, Bob)",
  "Server -> Alice : (pk(Bob), Bob) <:1f510:> skServer",
  "Alice -> Alice: <:1f513:> pkServer",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -> Bob: <:1f513:> skBob",
  "Bob -> Server: (Bob, Alice)",
  "Server -> Bob : (pkAlice, Alice) <:1f510:> skServer",
  "Bob -> Bob: <:1f513:> pkServer",
  "Bob -> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Alice: <:1f513:> skAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "Bob -> Bob: <:1f513:> skBob",
  "@enduml"
  ]

plantUMLTextNSPK7_dot :: Handler Text
plantUMLTextNSPK7_dot = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "database Server #green",
  "actor Bob #red",
  "Alice -[#0000FF]-> Server : (Alice, Bob)",
  "Server -[#0000FF]-> Alice : (pk(Bob), Bob) <:1f510:> skServer",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -[#0000FF]-> Server: (Bob, Alice)",
  "Server -[#0000FF]-> Bob : (pkAlice, Alice) <:1f510:> skServer",
  "Bob -> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "@enduml"
  ]

plantUMLTextNSPK3 :: Handler Text
plantUMLTextNSPK3 = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "actor Bob #red",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "@enduml"
  ]

plantUMLTextNSLPK3 :: Handler Text
plantUMLTextNSLPK3 = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "actor Bob #red",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -> Alice: (na, nb, <font color=red><b>Bob</font>) <:1f510:> pkAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "@enduml"
  ]

plantUMLTextNSPK3_attack :: Handler Text
plantUMLTextNSPK3_attack = return $ T.unlines $ [
  "@startuml",
  "title",
  "  Assume all participants know each other's <u>public keys</u>",
  "end title",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "entity \"Intruder <:spider:>\" as Intruder #green ",
  "actor Bob #red",
  "Alice -> Intruder: (na, Alice) <:1f510:> pkIntruder",
  "note left Intruder: Intruder decrypts and \\nthen re-encrypts it",
  "Intruder -[#red]> Bob : (na, Alice) <:1f510:> pkBob",
  "Bob -> Intruder: (na, nb) <:1f510:> pkAlice",
  "note left Intruder: Intruder cannot decrypt it \\nand so just forward it",
  "Intruder -[#red]> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Intruder: nb <:1f510:> pkIntruder",
  "note left Intruder: Intruder \\nknows <font color=red><b>nb</font>",
  "Intruder -[#red]> Bob: nb <:1f510:> pkBob",
  "note left Bob: But Bob <font color=red><b>doesn't realise</font>",
  "Caption The man-in-the-middle attack",
  "@enduml"
  ]

plantUMLTextNSLPK3_no_attack :: Handler Text
plantUMLTextNSLPK3_no_attack = return $ T.unlines $ [
  "@startuml",
  "title",
  "  Assume all participants know each other's <u>public keys</u>",
  "end title",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "entity \"Intruder <:spider:>\" as Intruder #green ",
  "actor Bob #red",
  "Alice -> Intruder: (na, Alice) <:1f510:> pkIntruder",
  "note left Intruder: Intruder decrypts and \\nthen re-encrypts it",
  "Intruder -[#red]> Bob : (na, Alice) <:1f510:> pkBob",
  "Bob -> Intruder: (na, nb, <font color=red><b>Bob</font>) <:1f510:> pkAlice",
  "note left Intruder: Intruder cannot decrypt it \\nand so just forward it",
  "Intruder -[#red]> Alice: (na, nb, Bob) <:1f510:> pkAlice",
  "note left Alice: Alice expects the message from Intruder \\n but it is from <font color=red><b>Bob</font>",
  "Caption No man-in-the-middle attack",
  "@enduml"
  ]
-- Define our data that will be used for creating the form.
data ManualInputForm = ManualInputForm
    { -- manualInput :: Int 
      manualSelectedEventId :: (Text, Text, Text, Text, Text)
    } deriving (Eq, Show)

-- User input for automatic reachability check: an event for monitoring and an event for checking
data AutoInputForm = AutoInputForm
    { 
      autoReach :: CheckMode, 
      autoMonitorChannel :: Text,
      autoMonitorMsg :: Maybe Text,
      autoCheckChannel :: Text,
      autoCheckMsg :: Maybe Text
    } deriving (Eq, Show)

manualInputForm :: [(Text, (Text, Text, Text, Text, Text))] -> Form ManualInputForm
manualInputForm eventList = 
  identifyForm "manualInputForm" $
  renderDivs $ ManualInputForm
    <$> areq (selectFieldList (eventList)) "Which event to animate?   " Nothing 

{-
autoAnimationForm :: [(Text, Text)] -> Form AutoInputForm
autoAnimationForm channelList = renderTable $ AutoInputForm
    <$> areq (selectFieldList channelList) "Choose a channel\t: \t" Nothing 
    <*> aopt textField "Type a message to check (optional)\t:\t " Nothing 
-}

{-
autoAnimationForm :: [(Text, Text)] -> Form AutoInputForm
autoAnimationForm channelList = renderTable $ AutoInputForm
    <$> areq (selectFieldList channelList) "Choose a channel\t: \t" Nothing 
    <*> aopt textField "Type a message to check (optional)\t:\t " Nothing
-}

autoAnimationForm :: [(Text, Text)] -> Form AutoInputForm
autoAnimationForm channelList = 
  identifyForm "autoAnimationForm" $
  renderBootstrap3 (BootstrapHorizontalForm (ColSm 0) (ColSm 5) (ColSm 0) (ColSm 6)) $ AutoInputForm
    <$> areq (radioFieldList reachFieldList) "Security check: " (Just Secrecy) 
    <*> areq (selectFieldList ([("", "")] ++ channelList)) "Choose a channel for monitoring: " (Just "")
    <*> aopt textField (textSettings "Type a message for monitoring (optional):") Nothing
    <*> areq (selectFieldList channelList) "Choose a channel for checking: " Nothing 
    <*> aopt textField (textSettings "Type a message for checking (optional):") Nothing
    <* submit "Automatic checking"
    -- Add attributes like the placeholder and CSS classes.
    where
        reachFieldList :: [(Text, CheckMode)]
        reachFieldList = 
            [ ("Secrecy/Reachability check - should not be reached", Secrecy)
            , ("Correspondence check - event 1 occurs before event 2", Correspondence)
            ] 
        textSettings label = FieldSettings
            { fsLabel = label 
            , fsTooltip = Nothing
            , fsId = Nothing
            , fsName = Nothing
            , fsAttrs =
                [ ("class", "form-control")
                , ("placeholder", "Message")
                ]
            }

{-
autoAnimationAForm :: [(Text, Text)] -> AForm Handler AutoInputForm
autoAnimationAForm channelList = AutoInputForm
    <$> areq (selectFieldList channelList) "Choose a channel\t: \t" Nothing 
    <*> aopt textField "Type a message to check (optional)\t:\t " (Just "*")

autoAnimationForm :: [(Text, Text)] -> Html -> Handler (FormResult AutoInputForm, Widget)
autoAnimationForm channelList = renderTable (autoAnimationAForm channelList)
-}

-- | The exploration bounds (depth, internal depth) for a protocol.  The values
--   differ a lot between protocols -- NSPK3 saturates at depth 15 (~95 s), while
--   NSWJ3 does not even finish at depth 20 -- so a protocol may override the
--   defaults in @config/settings.yml@ under @event-tree-bounds@.
getEventTreeDepthFor :: Text -> Handler (Int, Int)
getEventTreeDepthFor protocol = do
    app <- getYesod
    let settings = appSettings app
        defaults = (appEventTreeDepth settings, appEventTreeInternalDepth settings)
    return $ fromMaybe defaults (lookup protocol (appEventTreeBounds settings))

-- | The default exploration bounds, used by protocols without an override.
getEventTreeDepth :: Handler (Int, Int)
getEventTreeDepth = do 
    -- Get the foundation (App)
    app <- getYesod

    -- Access appSettings from the foundation
    let settings = appSettings app

    -- Extract specific settings, e.g., appTitle
    return $ (appEventTreeDepth settings, appEventTreeInternalDepth settings)


-- | Our definition of submit button.
submit :: MonadHandler m => Text -> AForm m ()
submit t = bootstrapSubmit (BootstrapSubmit t "btn-primary" [])

splitWhen' :: (Char -> Bool) -> String -> [String]
splitWhen' p s =  case DL.dropWhile p s of
   "" -> []
   s' -> w : splitWhen' p s''
         where (w, s'') = Import.break p s'

splitOn :: Char -> String -> [String]
splitOn c = splitWhen' (== c)

-- | The session key for protocol name 
sessionProtocolNameKey :: Text
sessionProtocolNameKey = "protocol"

-- | The session key for indexed counterexamples
sessionCounterexampleKey :: Text
sessionCounterexampleKey = "counterexample_"

-- | The session key for number of counterexamples
sessionNumberOfCounterexamplesKey :: Text
sessionNumberOfCounterexamplesKey = "number_of_counterexamples"

-- | The session key for PlantUML input for a chosen counterexample to view
sessionCntExPlantumlInputKey :: Text
sessionCntExPlantumlInputKey = "plantuml_input_cntex"

-- | How many tree rows are inserted per transaction.  Small enough that the
--   SQLite write lock is released between chunks, so a page request that writes
--   the session is not starved by a long build.
treeInsertChunk :: Int
treeInsertChunk = 200

-- | Split a list into chunks of at most @n@ elements.
chunksOfN :: Int -> [a] -> [[a]]
chunksOfN _ [] = []
chunksOfN n xs = let (h, t) = DL.splitAt n xs in h : chunksOfN n t

-- | Has a protocol tree been built completely?  The event rows are inserted in
--   one transaction together with a @TreeBuilt@ marker, so the marker is what
--   says "this tree is complete" -- a tree whose build was interrupted has no
--   marker and is rebuilt.
treeBuilt :: Text -> Text -> DB Bool
treeBuilt protocol eve = do
    rows <- selectList [TreeBuiltProtocol ==. protocol, TreeBuiltEve ==. eve] [LimitTo 1]
    case rows of
      []    -> return False
      (_:_) -> return True

-- | Record a completed tree.  Called inside the same transaction as the rows.
markTreeBuilt :: Text -> Text -> DB ()
markTreeBuilt protocol eve = insert_ (TreeBuilt protocol eve)

-- | Ensure a protocol tree is present and complete: build it, under the
--   protocol's lock, unless its completion marker is already there.
ensureTreeBuilt :: Text -> Text -> Handler () -> Handler ()
ensureTreeBuilt protocol eve build = do
    built <- runDB $ treeBuilt protocol eve
    if built then return () else
      liftHandler $ withTreeBuildLock protocol $ do
        builtAgain <- runDB $ treeBuilt protocol eve
        if builtAgain then return () else build

-- | Serialise the (expensive) construction of a protocol event tree.  The tree
--   is built on the first request that finds its table empty, which can take
--   minutes; every build is wrapped in this lock and re-checks the table inside
--   it, so a concurrent first request waits instead of building a second tree.
withTreeBuildLock :: Text -> Handler a -> Handler a
withTreeBuildLock protocol action = do
    app <- getYesod
    let locks = appTreeBuildLocks app
    case M.lookup protocol locks of
      Nothing   -> action
      Just lock -> bracket_ (liftIO $ takeMVar lock) (liftIO $ putMVar lock ()) action

-- | The verdict of a bounded check.  The stored event tree only contains traces
--   within the exploration bounds, so a negative result is a statement about
--   those bounds and nothing more; the message says so explicitly.  When the
--   exploration also ran out of internal steps (@budget_hit@ from the
--   Isabelle-proved search), the result is not even exhaustive within those
--   bounds, and the message says that too.
boundedVerdict :: Int -> Int -> Int -> Bool -> Text
boundedVerdict depth internalDepth nCounterexamples budgetExhausted =
  (if nCounterexamples == 0
     then "No safety violation found within "
     else T.pack (show nCounterexamples) <> " counterexample(s) found within ")
  <> T.pack (show depth) <> " visible steps and "
  <> T.pack (show internalDepth) <> " internal steps"
  <> (if nCounterexamples == 0
        then " -- a bounded result: a violation may still exist beyond these bounds."
        else " -- a bounded result.")
  <> (if budgetExhausted
        then "  WARNING: the internal-step budget (mx = " <> T.pack (show internalDepth)
             <> ") was exhausted and the search was cut short, so this result is not"
             <> " exhaustive within these bounds -- re-run with a larger internal-step"
             <> " bound (event-tree-internal-depth) for a complete answer."
        else "")

-- | Whether the bounded exploration of a protocol/eavesdropper tag ran out of
--   internal steps.  @budget_hit@ is a pure traversal of the model: cheaper
--   than the full exploration, but not free (a few seconds for the largest
--   model).  It is triggered by an explicit user action, so the answer is
--   memoised for the lifetime of the process: the first check pays the cost and
--   the rest are instant.
ensureBudgetHit :: Text -> Handler Bool -> Handler Bool
ensureBudgetHit key compute = do
    app <- getYesod
    cached <- M.lookup key <$> readMVar (appBudgetHit app)
    case cached of
      Just b  -> return b
      Nothing -> do
        b <- compute
        modifyMVar_ (appBudgetHit app) (return . M.insert key b)
        return b

-- | Format an event for display by using the following pattern:
--   ch[src-->desc].msg
formatEventForDisplay :: Text -> Text -> Text -> Text -> Text
formatEventForDisplay ch src desc msg = ch <> "[" <> src <> "-->" <> desc <> "]" <> "." <> msg
