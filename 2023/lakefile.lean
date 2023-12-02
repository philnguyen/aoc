import Lake
open Lake DSL

package «2023-lean» where
  -- add package configuration options here

lean_lib Lib

@[default_target]
lean_exe P01 where
  root := `P01

@[default_target]
lean_exe P02 where
  root := `P02
