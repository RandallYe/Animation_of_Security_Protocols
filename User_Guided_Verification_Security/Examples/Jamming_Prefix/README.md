# Non-empty proper-prefix jamming example

`Jamming_Prefix_Example.thy` imports the artefact's `Sec_Messages` theory and
evaluates its existing `breakl` function. It does not redefine the inference
implementation or change either protocol model.

The concrete message type is `(2, 4, 4, 4, 2, 2, 4) dmsg`. The masks are:

- `short_mask = Bm (nmk 0) (nmk 1)`;
- `long_mask = Bm (nmk 0) (nmk 3)`;
- `other_mask = Bm (nmk 1) (nmk 1)`.

The length domain has four elements, so these indices do not wrap. The theory
checks that the short mask is non-empty and strictly below the long mask, and
that the mask from the other code is incomparable with the long mask.

The payload is `MNon (nmk 0)`, and the intercepted term is
`MJam (MWat payload (MBitm long_mask)) (MBitm short_mask)`.

| Initial knowledge | Payload in `set (breakl K)` |
| --- | --- |
| Intercepted term alone | `False` |
| Intercepted term and `MBitm short_mask` | `True` |
| Intercepted term and `MBitm other_mask` | `False` |

Each mask assertion and each outcome is checked by an Isabelle lemma using
`by eval`. A final `value` command reports the three outcomes together.
The successful recovery deliberately supplies the jamming mask as initial
knowledge. This is an inference-level configuration, not a claim that the mask
becomes known in an NSWJ or DHWJ execution.

## Reproduction

Use Isabelle2025 with the artefact's ITree dependencies installed. Set
`ARTEFACT` to the root of `Animation_of_Security_Protocols`, then set
`EXAMPLE_DIR` and build the supplied session:

```sh
EXAMPLE_DIR="$ARTEFACT/User_Guided_Verification_Security/Examples/Jamming_Prefix"
isabelle build \
  -d "$ARTEFACT/User_Guided_Verification_Security" \
  -d "$EXAMPLE_DIR" \
  -o document=false Jamming_Prefix_Example
```

Alternatively, with the `ITree_Security` heap already built, load the theory
directly to display the evaluation:

```sh
isabelle process \
  -d "$ARTEFACT/User_Guided_Verification_Security" \
  -l ITree_Security \
  -T "$EXAMPLE_DIR/Jamming_Prefix_Example"
```

## Recorded check

Checked on 2026-11-05 using Isabelle2025 and the local artefact checkout at
`2360f2b2544ae266b33114572894d9b47f957dbb`. Its `Sec_Messages.thy` and
`FSNat.thy` are unchanged from the manuscript's pinned release
`47410a4b04f2cd91e8e875264f96ce3cce89ecd4`.

The direct-load command above exited with status 0. All five lemmas passed;
the final evaluation printed:

```text
"[False, True, False]"
  :: "\<bool> list"
```

The check used a temporary Isabelle user directory and a copy of the existing
artefact heaps. The example was also checked after moving it into this
directory in the artefact repository. It is additional to the pinned release
and should be included in a future artefact release.
