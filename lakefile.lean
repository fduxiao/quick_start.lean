import Lake
open Lake DSL


meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"


package «quick_start» where
  -- add package configuration options here

lean_lib «QuickStart» where
  -- add library configuration options here

@[default_target]
lean_exe «quick_start» where
  root := `Main
