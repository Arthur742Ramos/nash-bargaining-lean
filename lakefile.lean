import Lake
open Lake DSL

package «nash_bargaining» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

@[default_target]
lean_lib NashBargaining where
  roots := #[
    `NashBargaining.Basic,
    `NashBargaining.Existence,
    `NashBargaining.Uniqueness,
    `NashBargaining.Characterization]

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
