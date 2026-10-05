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
  eventList, eventTreeList, formatEvents, formatTEvent, formatTEvents, getChannelList, getChannelList4Property,
  -- the sound (Isabelle-proved) bounded exploration and its checks
  explore, checks, feasible, reaches, is_leak, is_sig, is_start, is_end, is_terminate,
  check_leak, check_leak_msg, check_sig, check_terminate, check_corr, check_corr_violation, check_authenticity,
  nat_of_integer, secSetToList
  ) where
import Interaction_Trees( Itree(..));
import Sec_Animation (explore, checks, state_kind, Skind(..), feasible, reaches, is_leak, is_sig, is_start, is_end, is_terminate,
  check_leak, check_leak_msg, check_sig, check_terminate, check_corr, check_corr_violation, check_authenticity);
import Prelude;
import Text.Read (get);
import Text.Show.Pretty ( ppShow );
import System.IO ();
import Arith ( Nat(Nat), nat_of_integer );
import qualified Set;
import FSNat;
import Sec_Messages ( Chan(..), Dmsg(..), Dsig(..), Dagent(Agent), Dkey(Kp, Ks));
import Numeral_Type;
import qualified Type_Length;
import qualified Data.List as List (sortBy, groupBy);
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

-- | Elements of a finite set, in the order in which the extracted search built it.
secSetToList :: Set.Set a -> [a]
secSetToList (Set.Set xs) = xs
secSetToList (Set.Coset _) = []

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

-- | The traces of the sound (Isabelle-proved) bounded exploration of a model,
--   with the empty trace (the root) removed.  Both soundness and bounded
--   completeness are inherited from @explore@ of @Sec_Animation@.
soundTraces p steps tau_steps =
  filter (not . null)
    (secSetToList (explore (nat_of_integer (fromIntegral steps))
                           (nat_of_integer (fromIntegral tau_steps))
                           (nat_of_integer (fromIntegral tau_steps)) p))

-- | The event tree of a list of traces, all of which share the current prefix,
--   over the model @p@ with internal-step bound @tau@.
soundTree p tau trs = ETNode (TEP 0 0 Root) (soundForest p tau 1 [] trs)

-- | The children of a node at depth @d@ reached by the trace @prefix@: the
--   events the model can perform next, in the canonical order of the shown
--   events (the sibling number is the position in that order), followed by the
--   leaf label of @prefix@ when the run stops there.  The label comes from the
--   Isabelle-proved @state_kind@ oracle, so a leaf really is a finished,
--   deadlocked or divergent run.
soundForest p tau d prefix trs =
  eventChildren ++ kindChildren
  where
    groups = List.groupBy (\x y -> show (head x) == show (head y))
               (List.sortBy (\x y -> compare (show (head x)) (show (head y)))
                  (filter (not . null) trs))
    eventChildren =
      [ ETNode (TEP d i (EChan e)) (soundForest p tau (d + 1) (prefix ++ [e]) (map tail g))
      | (i, g) <- zip [1..] groups, let e = head (head g) ]
    kindChildren = case state_kind (nat_of_integer (fromIntegral tau)) p prefix of
      SContinues  -> []
      STerminated -> [ETNode (TEP (d + 1) 0 Terminated) []]
      SDeadlocked -> [ETNode (TEP (d + 1) 0 Deadlocked) []]
      SDivergent  -> [ETNode (TEP (d + 1) 0 Divergent) []]

-- | A top-level function to explore an ITree for given steps of external events and internal events.
--   The tree is built from the traces of the sound (Isabelle-proved) bounded exploration, so every
--   node stored in the database is a genuine trace and every trace within the bounds is present.
explore_tree_NSPK3 :: Int -> Int -> EventTree 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1)
explore_tree_NSPK3 steps tau_steps = soundTree nSPK3 tau_steps (soundTraces nSPK3 steps tau_steps)

-- | A top-level function to explore an ITree for given steps of external events and internal events.
--   As for @explore_tree_NSPK3@, the tree comes from the sound bounded exploration.
explore_tree_NSLPK3 :: Int -> Int -> EventTree 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1)
explore_tree_NSLPK3 steps tau_steps = soundTree nSLPK3 tau_steps (soundTraces nSLPK3 steps tau_steps)
