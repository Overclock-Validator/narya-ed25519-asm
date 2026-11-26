/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Executable specification of Narya's DalekStrict Ed25519 verifier. It imports
only Lean core so the compiled checker (`lake exe narya-spec-check`) runs the
same definitions the proofs will refer to.
-/

import NaryaSpec.Bytes
import NaryaSpec.Sha512
import NaryaSpec.Field
import NaryaSpec.Edwards
import NaryaSpec.Verify
