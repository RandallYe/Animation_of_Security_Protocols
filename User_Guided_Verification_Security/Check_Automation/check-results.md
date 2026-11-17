# Check — reproduced 2026-10-29 21:30 UTC

Bounds (visible events / internal steps): nspk3 [15 100] nslpk3 [15 100] nswj3 [15 100] dhwj [15 100] dh [15 100]; budget retries: 2 x2

| Protocol | Model | Secrecy | Auth (Alice) | Auth (Bob) | Budget |
|---|---|---|---|---|---|
| nspk3 | nSPK3 | ○ | ● | ○ | ok |
| nslpk3 | nSLPK3 | ● | ● | ● | ok |
| nswj3 | nSWJ3_active_eve1 | ○ | ● | ● | ok |
| nswj3 | nSWJ3_active_eve2 | ○ | ● | ● | ok |
| nswj3 | nSWJ3_active_eve3 | ● | ● | ● | ok |
| nswj3 | nSWJ3_active_eve4 | ○ | ● | ● | ok |
| nswj3 | nSWJ3_passive_eve1 | ○ | ● | ● | ok |
| nswj3 | nSWJ3_passive_eve2 | ○ | ● | ● | ok |
| nswj3 | nSWJ3_passive_eve3 | ● | ● | ● | ok |
| nswj3 | nSWJ3_passive_eve4 | ○ | ● | ● | ok |
| dhwj | dHWJ_active_eve1 | ● | ● | ● | ok |
| dhwj | dHWJ_active_eve2 | ● | ● | ● | ok |
| dhwj | dHWJ_active_eve3 | ● | ● | ● | ok |
| dhwj | dHWJ_active_eve4 | ● | ● | ● | ok |
| dh | dH_Original | ○ | ● | ● | ok |

A `?` marks a cell whose search exhausted the internal-step budget (or did not finish); it is not a verdict. `Budget` is `ok` only when no property of that model exhausted its budget.
