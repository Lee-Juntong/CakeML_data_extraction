import Lake
open Lake DSL

package «CML_Lean» where
  -- add package configuration options here

lean_lib «CML_Lean» where
  -- add library configuration options here

@[default_target]
lean_exe «cml_lean» where
  root := `Main
