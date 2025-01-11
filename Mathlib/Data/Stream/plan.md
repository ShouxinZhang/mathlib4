feat: check that every file imports Mathlib.Init

We add a purely text-based check to the `lint-style` script,
that every file either (transivively) imports Mathlib.Init,
or is (transitively) imported by it.


-- First, we find any file in the Mathlib directory which does not contain
-- any Mathlib import, i.e. no line starting with "import Mathlib".
-- This is not absolutely error-proof (for instance, would not detect a multi-line
comment containing the line import Mathlib), but is good enough in practice.

-- We check that each of these is imported in Mathlib.Init.
-- (DeclarationNames is transitively imported here, this is also fine.)



-- Secondly, after #... almost all files imported in Mathlib.Init impor the `header`
-- linter defined in `Mathlib.Tactic.Linter.Header`: so, we verify that the only
-- files importing it are also imported in Mathlib.Init.

-- xxx. The Header linter itself is also fine.
