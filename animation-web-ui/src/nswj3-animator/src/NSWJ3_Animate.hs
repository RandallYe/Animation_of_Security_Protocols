{-|
Module      :  Animate
Copyright   :  (c) Kangfeng Ye, 2025 
License     :  BSD3

Maintainer  :  Kangfeng Ye <kangfeng.ye@york.ac.uk>
Stability   :  experimental

This module provides functions to animate the interaction trees. 
-}

{-# LANGUAGE StandaloneDeriving #-}

module NSWJ3_Animate (explore_tree_NSWJ3, 
  EventTree(ETNode), TEventPos(TEP), TEvent(Root, Deadlocked, Terminated, Divergent, EChan),
  NSWJ3_TEvent(..), NSWJ3_EventTree(..), eventList, eventTreeList, formatEvents, formatTEvent, formatTEvents, 
  getChannelList, getChannelList4Property,
  explore, checks, budgetExhausted, nat_of_integer, secSetToList
  ) where
import Interaction_Trees ( Itree(..), Pfun(Pfun_of_alist, Pfun_of_map, Pfun_entries), pfun_app );
import Prelude;
import Text.Read (get);
import Text.Show.Pretty ( ppShow );
import System.IO ();
import Arith ( Nat(Nat), nat_of_integer );
import qualified Set;
import Sec_Messages ( Chan(..), Dmsg(..), Dsig(..), Dagent(Agent), Dkey(Kp, Ks));
import qualified Numeral_Type;
import qualified Type_Length;
-- import qualified Data.List (dropWhile, dropWhileEnd, intersect, head, tail, elemIndex, uncons);
import Sec_Animation (explore, checks, budget_hit, state_kind, Skind(..));
import qualified Data.List as List (sortBy, groupBy);
-- import Control.Monad (forM_, when);
-- import System.Exit (exitWith, ExitCode( ExitSuccess ));
-- import System.Random.Stateful ();
-- import Data.Char (isSpace); 
import Simulate (ppAgent, ppMsg, ppSig, ppK, ppG, ppNmk, ppNonce, ppSet, ppList, ppTrace, ppTraceApp, 
  format_events, format_reach, simulate_cnt, eventList, eventTreeList, formatEvents,
  TEvent(..), TEventPos(..), EventTree(..), formatTEvent, formatTEvents, explore_tree_cnt, getChannelList, getChannelList4Property);
import NSWJ3_config (Deve(..), mkbma)
import NSWJ3_wbplsec (nSWJ3_active)

-- | Elements of a finite set, in the order in which the extracted search built it.
secSetToList :: Set.Set a -> [a]
secSetToList (Set.Set xs) = xs
secSetToList (Set.Coset _) = []

-- | The traces of the sound (Isabelle-proved) bounded exploration, without the root.
soundTraces p steps tau_steps =
  filter (not . null)
    (secSetToList (explore (nat_of_integer (fromIntegral steps))
                           (nat_of_integer (fromIntegral tau_steps))
                           (nat_of_integer (fromIntegral tau_steps)) p))

-- | The event tree of a list of traces, all of which share the current prefix.
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

newtype NSWJ3_TEvent = NSWJ3_TEvent (TEvent 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 
  (Numeral_Type.Bit1 Numeral_Type.Num1)
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  )
  deriving (Eq, Read, Show);

newtype NSWJ3_EventTree = NSWJ3_EventTree (EventTree 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 
  (Numeral_Type.Bit1 Numeral_Type.Num1)
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  )
  deriving (Eq, Read, Show);

-- | The configuration datatype is compared structurally.
deriving instance Eq Deve;

-- | A top-level function to explore an ITree for given steps of external events and internal events 
explore_tree_NSWJ3 ::  Int -> Int -> Deve -> EventTree
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 
  (Numeral_Type.Bit1 Numeral_Type.Num1)
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  ;
explore_tree_NSWJ3 steps tau_steps eve = soundTree (nSWJ3_active eve) tau_steps (soundTraces (nSWJ3_active eve) steps tau_steps)

-- | Was the bounded exploration of this eavesdropper scenario cut short because
--   the internal-step budget ran out?  If so, a bounded verdict is not
--   exhaustive within the bounds and the internal-step bound should be raised.
budgetExhausted :: Int -> Int -> Deve -> Bool
budgetExhausted steps tau_steps eve =
  budget_hit (nat_of_integer (fromIntegral steps))
             (nat_of_integer (fromIntegral tau_steps))
             (nat_of_integer (fromIntegral tau_steps)) (nSWJ3_active eve)