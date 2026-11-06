theory Jamming_Prefix_Example
  imports "ITree_Security.Sec_Messages"
begin

text \<open>A term-level example of Jam1 with a non-empty proper prefix.
  The known-prefix case deliberately supplies the jamming mask as knowledge;
  it is not a reachable-state claim about NSWJ or DHWJ.\<close>

type_synonym example_msg = "(2, 4, 4, 4, 2, 2, 4) dmsg"

definition short_mask :: "(2, 4) dbitmask" where
  "short_mask = Bm (nmk 0) (nmk 1)"

definition long_mask :: "(2, 4) dbitmask" where
  "long_mask = Bm (nmk 0) (nmk 3)"

definition other_mask :: "(2, 4) dbitmask" where
  "other_mask = Bm (nmk 1) (nmk 1)"

definition payload :: example_msg where
  "payload = mknon 0"

definition jammed :: example_msg where
  "jammed = MJam (MWat payload (MBitm long_mask)) (MBitm short_mask)"

lemma nonempty_proper_prefix:
  "short_mask \<noteq> Null \<and> short_mask < long_mask"
  by eval

lemma different_code_incomparable:
  "\<not> other_mask \<le> long_mask \<and> \<not> long_mask \<le> other_mask"
  by eval

lemma unknown_prefix:
  "payload \<notin> set (breakl [jammed])"
  by eval

lemma known_proper_prefix:
  "payload \<in> set (breakl [jammed, MBitm short_mask])"
  by eval

lemma wrong_code:
  "payload \<notin> set (breakl [jammed, MBitm other_mask])"
  by eval

value "map (\<lambda>K. payload \<in> set (breakl K))
  [[jammed], [jammed, MBitm short_mask], [jammed, MBitm other_mask]]"

end
