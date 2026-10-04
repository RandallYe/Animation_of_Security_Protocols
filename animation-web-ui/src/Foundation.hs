{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}

module Foundation where

import Import.NoFoundation
import Data.Kind            (Type)
import Database.Persist.Sql (ConnectionPool, runSqlPool)
import Text.Hamlet          (hamletFile)
import Text.Jasmine         (minifym)
import Control.Monad.Logger (LogSource)

-- Used only when in "auth-dummy-login" setting is enabled.
import Yesod.Auth.Dummy

import Yesod.Auth.OpenId    (authOpenId, IdentifierType (Claimed))
import Yesod.Default.Util   (addStaticContentExternal)
import Yesod.Core.Types     (Logger)
import qualified Yesod.Core.Unsafe as Unsafe
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE

-- Assuming you use SessionMap as your session data type
-- import Web.ServerSession.Backend.Acid (AcidStorage(..), emptyState) 
-- import Web.ServerSession.Frontend.Yesod (simpleBackend)
-- import Data.Acid (openLocalState)

import Web.ServerSession.Backend.Persistent
import Web.ServerSession.Frontend.Yesod

-- | The foundation datatype for your application. This can be a good place to
-- keep settings and values requiring initialization before your application
-- starts running, such as database connections. Every handler will have
-- access to the data present here.
data App = App
    { appSettings    :: AppSettings
    , appStatic      :: Static -- ^ Settings for static file serving.
    , appConnPool    :: ConnectionPool -- ^ Database connection pool.
    , appHttpManager :: Manager
    , appLogger      :: Logger
    , appTreeBuildLocks :: Map Text (MVar ())
    -- ^ One lock per protocol, serialising the construction of its event tree.
    --   A tree is built by the first request that finds its table empty (or by
    --   the startup preload), and that exploration can take minutes; without
    --   the lock two concurrent builders would do the work twice and the second
    --   would hit the unique index on the event id.
    }

data MenuItem = MenuItem
    { menuItemLabel :: Text
    , menuItemRoute :: Route App
    , menuItemAccessCallback :: Bool
    }

data MenuTypes
    = NavbarLeft MenuItem
    | NavbarRight MenuItem

-- This is where we define all of the routes in our application. For a full
-- explanation of the syntax, please see:
-- http://www.yesodweb.com/book/routing-and-handlers
--
-- Note that this is really half the story; in Application.hs, mkYesodDispatch
-- generates the rest of the code. Please see the following documentation
-- for an explanation for this split:
-- http://www.yesodweb.com/book/scaffolding-and-the-site-template#scaffolding-and-the-site-template_foundation_and_application_modules
--
-- This function also generates the following type synonyms:
-- type Handler = HandlerFor App
-- type Widget = WidgetFor App ()
mkYesodData "App" $(parseRoutesFile "config/routes.yesodroutes")

-- | A convenient synonym for creating forms.
type Form x = Html -> MForm (HandlerFor App) (FormResult x, Widget)

-- | A convenient synonym for database access functions.
type DB a = forall (m :: Type -> Type).
    (MonadUnliftIO m) => ReaderT SqlBackend m a

-- | Cookie name used for the sessions of this example app.
sessionCookieName :: Text
sessionCookieName = "Animator-Session"

-- Please see the documentation for the Yesod typeclass. There are a number
-- of settings which can be configured by overriding methods here.
instance Yesod App where
    -- Controls the base of generated URLs. For more information on modifying,
    -- see: https://github.com/yesodweb/yesod/wiki/Overriding-approot
    approot :: Approot App
    approot = ApprootRequest $ \app req ->
        case appRoot $ appSettings app of
            Nothing -> getApprootText guessApproot app req
            Just root -> root

    -- Store session data using server-side sessions.  Change the
    -- timeouts to small values as this is just an example (so
    -- that you can wait for the idle timeout, for example).
    makeSessionBackend = simpleBackend opts . SqlStorage . appConnPool
      where opts = setIdleTimeout     (Just $  5 * 60) -- 5  minutes
                 . setAbsoluteTimeout (Just $ 20 * 60) -- 20 minutes
                 . setCookieName      sessionCookieName

    -- Yesod Middleware allows you to run code before and after each handler function.
    -- The defaultYesodMiddleware adds the response header "Vary: Accept, Accept-Language" and performs authorization checks.
    -- Some users may also want to add the defaultCsrfMiddleware, which:
    --   a) Sets a cookie with a CSRF token in it.
    --   b) Validates that incoming write requests include that token in either a header or POST parameter.
    -- To add it, chain it together with the defaultMiddleware: yesodMiddleware = defaultYesodMiddleware . defaultCsrfMiddleware
    -- For details, see the CSRF documentation in the Yesod.Core.Handler module of the yesod-core package.
    yesodMiddleware :: ToTypedContent res => Handler res -> Handler res
    yesodMiddleware = defaultYesodMiddleware

    defaultLayout :: Widget -> Handler Html
    defaultLayout widget = do
        master <- getYesod
        mmsg <- getMessage

        muser <- maybeAuthPair
        mcurrentRoute <- getCurrentRoute

        -- Get the breadcrumbs, as defined in the YesodBreadcrumbs instance.
        (title, parents) <- breadcrumbs

        -- Define the menu items of the header.
        let menuItems =
                [ NavbarLeft $ MenuItem
                    { menuItemLabel = "Home"
                    , menuItemRoute = HomeR
                    , menuItemAccessCallback = True
                    }
                , NavbarLeft $ MenuItem
                    { menuItemLabel = "Sessions"
                    , menuItemRoute = SessionR
                    , menuItemAccessCallback = True 
                    }
                , NavbarRight $ MenuItem
                    { menuItemLabel = "Animate NSPK3"
                    , menuItemRoute = AnimateNSPK3R
                    , menuItemAccessCallback = True 
                    }
                , NavbarRight $ MenuItem
                    { menuItemLabel = "Animate NSLPK3"
                    , menuItemRoute = AnimateNSLPK3R
                    , menuItemAccessCallback = True 
                    }
                , NavbarRight $ MenuItem
                    { menuItemLabel = "Animate NSWJ3"
                    , menuItemRoute = AnimateNSWJ3R
                    , menuItemAccessCallback = True 
                    }
                , NavbarRight $ MenuItem
                    { menuItemLabel = "Animate DHWJ"
                    , menuItemRoute = AnimateDHWJR
                    , menuItemAccessCallback = True 
                    }
                ]

        let navbarLeftMenuItems = [x | NavbarLeft x <- menuItems]
        let navbarRightMenuItems = [x | NavbarRight x <- menuItems]

        let navbarLeftFilteredMenuItems = [x | x <- navbarLeftMenuItems, menuItemAccessCallback x]
        let navbarRightFilteredMenuItems = [x | x <- navbarRightMenuItems, menuItemAccessCallback x]

        -- We break up the default layout into two components:
        -- default-layout is the contents of the body tag, and
        -- default-layout-wrapper is the entire page. Since the final
        -- value passed to hamletToRepHtml cannot be a widget, this allows
        -- you to use normal widget features in default-layout.

        pc <- widgetToPageContent $ do
            addStylesheet $ StaticR css_bootstrap_css
                                    -- ^ generated from @Settings/StaticFiles.hs@
            $(widgetFile "default-layout")
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")

    -- The page to be redirected to when authentication is required.
--    authRoute
--        :: App
--        -> Maybe (Route App)
--    authRoute _ = Just $ AuthR LoginR

    isAuthorized
        :: Route App  -- ^ The route the user is visiting.
        -> Bool       -- ^ Whether or not this is a "write" request.
        -> Handler AuthResult
    -- Routes not requiring authentication.
--    isAuthorized (AuthR _) _ = return Authorized
--    isAuthorized CommentR _ = return Authorized
    isAuthorized HomeR _ = return Authorized
    isAuthorized FaviconR _ = return Authorized
    isAuthorized RobotsR _ = return Authorized
    isAuthorized (StaticR _) _ = return Authorized

    -- the profile route requires that the user is authenticated, so we
    -- delegate to that function
--    isAuthorized ProfileR _ = isAuthenticated
    isAuthorized (SessionAddR) _ = return Authorized
    isAuthorized (SessionDeleteR _) _ = return Authorized
    isAuthorized (SessionR) _ = return Authorized
    isAuthorized (SessionClearR) _ = return Authorized
    isAuthorized (AnimateNSPK3R) _ = return Authorized
    isAuthorized (AnimateNSPK3AutoR) _ = return Authorized
    isAuthorized (AnimateNSPK3ResetR) _ = return Authorized
    isAuthorized (ViewNSPK3CounterExampleR _) _ = return Authorized
    isAuthorized (AnimateNSLPK3R) _ = return Authorized
    isAuthorized (AnimateNSLPK3AutoR) _ = return Authorized
    isAuthorized (AnimateNSLPK3ResetR) _ = return Authorized
    isAuthorized (ViewNSLPK3CounterExampleR _) _ = return Authorized
    isAuthorized (AnimateNSWJ3R) _ = return Authorized
    isAuthorized (AnimateNSWJ3AutoR) _ = return Authorized
    isAuthorized (AnimateNSWJ3ResetR) _ = return Authorized
    isAuthorized (ViewNSWJ3CounterExampleR _) _ = return Authorized
    isAuthorized (ChangeNSWJ3ProtocolR) _ = return Authorized
    isAuthorized (AnimateDHWJR) _ = return Authorized
    isAuthorized (AnimateDHWJAutoR) _ = return Authorized
    isAuthorized (AnimateDHWJResetR) _ = return Authorized
    isAuthorized (ViewDHWJCounterExampleR _) _ = return Authorized
    isAuthorized (ChangeDHWJProtocolR) _ = return Authorized

    -- This function creates static content files in the static folder
    -- and names them based on a hash of their content. This allows
    -- expiration dates to be set far in the future without worry of
    -- users receiving stale content.
    addStaticContent
        :: Text  -- ^ The file extension
        -> Text -- ^ The MIME content type
        -> LByteString -- ^ The contents of the file
        -> Handler (Maybe (Either Text (Route App, [(Text, Text)])))
    addStaticContent ext mime content = do
        master <- getYesod
        let staticDir = appStaticDir $ appSettings master
        addStaticContentExternal
            minifym
            genFileName
            staticDir
            (StaticR . flip StaticRoute [])
            ext
            mime
            content
      where
        -- Generate a unique filename based on the content itself
        genFileName lbs = "autogen-" ++ base64md5 lbs

    -- What messages should be logged. The following includes all messages when
    -- in development, and warnings and errors in production.
    shouldLogIO :: App -> LogSource -> LogLevel -> IO Bool
    shouldLogIO app _source level =
        return $
        appShouldLogAll (appSettings app)
            || level == LevelWarn
            || level == LevelError

    makeLogger :: App -> IO Logger
    makeLogger = return . appLogger

-- Define breadcrumbs.
instance YesodBreadcrumbs App where
    -- Takes the route that the user is currently on, and returns a tuple
    -- of the 'Text' that you want the label to display, and a previous
    -- breadcrumb route.
    breadcrumb
        :: Route App  -- ^ The route the user is visiting currently.
        -> Handler (Text, Maybe (Route App))
    breadcrumb HomeR = return ("Home", Nothing)
--    breadcrumb (AuthR _) = return ("Login", Just HomeR)
--    breadcrumb ProfileR = return ("Profile", Just HomeR)
    breadcrumb (SessionAddR) = return ("Session", Just HomeR)
    breadcrumb (SessionR) = return ("Session", Just HomeR)
    breadcrumb (SessionClearR) = return ("Session", Just HomeR)
    breadcrumb (AnimateNSPK3R) = return ("Animate NSPK3", Just HomeR)
    breadcrumb (AnimateNSPK3AutoR) = return ("Automatic checking (NSPK3)", Just HomeR)
    breadcrumb (ViewNSPK3CounterExampleR _) = return ("View counterexample in sequence diagram", Just AnimateNSPK3R)
    breadcrumb (AnimateNSLPK3R) = return ("Animate NSLPK3", Just HomeR)
    breadcrumb (AnimateNSLPK3AutoR) = return ("Automatic checking (NSLPK3)", Just HomeR)
    breadcrumb (ViewNSLPK3CounterExampleR _) = return ("View counterexample in sequence diagram", Just AnimateNSLPK3R)
    breadcrumb (AnimateNSWJ3R) = return ("Animate NSWJ3", Just HomeR)
    breadcrumb (AnimateNSWJ3AutoR) = return ("Automatic checking (NSWJ3)", Just HomeR)
    breadcrumb (ViewNSWJ3CounterExampleR _) = return ("View counterexample in sequence diagram", Just AnimateNSWJ3R)
    breadcrumb (ChangeNSWJ3ProtocolR) = return ("Change the location of Eavesdropper", Just AnimateNSWJ3R)
    breadcrumb (AnimateDHWJR) = return ("Animate DHWJ", Just HomeR)
    breadcrumb (AnimateDHWJAutoR) = return ("Automatic checking (DHWJ)", Just HomeR)
    breadcrumb (ViewDHWJCounterExampleR _) = return ("View counterexample in sequence diagram", Just AnimateDHWJR)
    breadcrumb (ChangeDHWJProtocolR) = return ("Change the location of Eavesdropper", Just AnimateDHWJR)
    breadcrumb  _ = return ("home", Nothing)

-- How to run database actions.
instance YesodPersist App where
    type YesodPersistBackend App = SqlBackend
    runDB :: SqlPersistT Handler a -> Handler a
    runDB action = do
        master <- getYesod
        runSqlPool action $ appConnPool master

instance YesodPersistRunner App where
    getDBRunner :: Handler (DBRunner App, Handler ())
    getDBRunner = defaultGetDBRunner appConnPool

instance YesodAuth App where
    type AuthId App = UserId

    -- Where to send a user after successful login
    loginDest :: App -> Route App
    loginDest _ = HomeR
    -- Where to send a user after logout
    logoutDest :: App -> Route App
    logoutDest _ = HomeR
    -- Override the above two destinations when a Referer: header is present
    redirectToReferer :: App -> Bool
    redirectToReferer _ = True

    authenticate :: (MonadHandler m, HandlerSite m ~ App)
                 => Creds App -> m (AuthenticationResult App)
    authenticate creds = liftHandler $ runDB $ do
        x <- getBy $ UniqueUser $ credsIdent creds
        case x of
            Just (Entity uid _) -> return $ Authenticated uid
            Nothing -> Authenticated <$> insert User
                { userIdent = credsIdent creds
                , userPassword = Nothing
                }

    -- You can add other plugins like Google Email, email or OAuth here
    authPlugins :: App -> [AuthPlugin App]
    authPlugins app = [authOpenId Claimed []] ++ extraAuthPlugins
        -- Enable authDummy login if enabled.
        where extraAuthPlugins = [authDummy | appAuthDummyLogin $ appSettings app]

-- | Access function to determine if a user is logged in.
isAuthenticated :: Handler AuthResult
isAuthenticated = do
    muid <- maybeAuthId
    return $ case muid of
        Nothing -> Unauthorized "You must login to access this page"
        Just _ -> Authorized

instance YesodAuthPersist App

-- This instance is required to use forms. You can modify renderMessage to
-- achieve customized and internationalized form validation messages.
instance RenderMessage App FormMessage where
    renderMessage :: App -> [Lang] -> FormMessage -> Text
    renderMessage _ _ = defaultFormMessage

-- Useful when writing code that is re-usable outside of the Handler context.
-- An example is background jobs that send email.
-- This can also be useful for writing code that works across multiple Yesod applications.
instance HasHttpManager App where
    getHttpManager :: App -> Manager
    getHttpManager = appHttpManager

unsafeHandler :: App -> Handler a -> IO a
unsafeHandler = Unsafe.fakeHandlerGetLogger appLogger

-- Note: Some functionality previously present in the scaffolding has been
-- moved to documentation in the Wiki. Following are some hopefully helpful
-- links:
--
-- https://github.com/yesodweb/yesod/wiki/Sending-email
-- https://github.com/yesodweb/yesod/wiki/Serve-static-files-from-a-separate-domain
-- https://github.com/yesodweb/yesod/wiki/i18n-messages-in-the-scaffolding
