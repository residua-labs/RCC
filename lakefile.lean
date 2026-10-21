import Lake
open Lake DSL

package «RCC» where

@[default_target]
lean_lib «RCC» where
  roots := #[`RCC]
  globs := #[.andSubmodules `RCC]

@[default_target]
lean_lib «RCCTests» where
  roots := #[`RCCTests]
  globs := #[.andSubmodules `RCCTests]
