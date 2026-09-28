{-|
Module      :  Animate
Copyright   :  (c) Kangfeng Ye, 2025 
License     :  BSD3

Maintainer  :  Kangfeng Ye <kangfeng.ye@york.ac.uk>
Stability   :  experimental

This module provides functions to animate the interaction trees. 
-}

{-# LANGUAGE RankNTypes #-}

module NSPK3_Animate (explore_tree_NSPK3, 
  explore_tree_NSLPK3, EventTree(ETNode), TEventPos(TEP), TEvent(Root, Deadlocked, Terminated, Divergent, EChan),
  NSPK3_TEvent(..), NSPK3_EventTree(..), NSLPK3_TEvent(..), NSLPK3_EventTree(..), 
  eventList, eventTreeList, formatEvents, formatTEvent, formatTEvents, getChannelList, getChannelList4Property
  ) where
import Interaction_Trees( Itree(..), Pfun(Pfun_of_alist, Pfun_of_map, Pfun_entries));
import Prelude;
import Text.Read (get);
import Text.Show.Pretty ( ppShow );
import System.IO ();
import Arith ( Nat(Nat) );
import qualified Set;
import FSNat;
import Sec_Messages ( Chan(..), Dmsg(..), Dsig(..), Dagent(Agent), Dkey(Kp, Ks));
import Numeral_Type;
import qualified Type_Length;
-- import qualified Data.List (dropWhile, dropWhileEnd, intersect, head, tail, elemIndex, uncons);
-- import Control.Monad (forM_, when);
-- import System.Exit (exitWith, ExitCode( ExitSuccess ));
-- import System.Random.Stateful ();
-- import Data.Char (isSpace); 
import Simulate (ppAgent, ppMsg, ppSig, ppK, ppG, ppNmk, ppNonce, ppSet, ppList, ppTrace, ppTraceApp, 
  format_events, format_reach, simulate_cnt, eventList, eventTreeList, formatEvents,
  TEvent(..), TEventPos(..), EventTree(..), formatTEvent, formatTEvents, explore_tree_cnt, getChannelList, getChannelList4Property);
import NSPK3 (nSPK3)
import NSLPK3 (nSLPK3)
-- import qualified Set;

newtype NSPK3_TEvent = NSPK3_TEvent (TEvent 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1))
  deriving (Eq, Read, Show);

newtype NSLPK3_TEvent = NSLPK3_TEvent (TEvent 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1))
  deriving (Eq, Read, Show);

newtype NSPK3_EventTree = NSPK3_EventTree (EventTree 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1))
  deriving (Eq, Read, Show);

newtype NSLPK3_EventTree = NSLPK3_EventTree (EventTree 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1))
  deriving (Eq, Read, Show);

-- | A top-level function to explore an ITree for given steps of external events and internal events 
explore_tree_NSPK3 :: Int -> Int -> EventTree 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1)
explore_tree_NSPK3 steps tau_steps = ETNode (TEP 0 0 Root) (explore_tree_cnt nSPK3 steps 1 tau_steps tau_steps)

-- | A top-level function to explore an ITree for given steps of external events and internal events 
explore_tree_NSLPK3 :: Int -> Int -> EventTree 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1)
explore_tree_NSLPK3 steps tau_steps = ETNode (TEP 0 0 Root) (explore_tree_cnt nSLPK3 steps 1 tau_steps tau_steps)
