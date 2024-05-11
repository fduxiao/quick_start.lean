import Lake
open Lake DSL

package «quick_start» where
  -- add package configuration options here

lean_lib «QuickStart» where
  -- add library configuration options here

@[default_target]
lean_exe «quick_start» where
  root := `Main
