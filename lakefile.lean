import Lake
open Lake DSL

package yinlang {
  srcDir := "src"
  -- add package configuration options here
}

lean_lib Syntax
lean_lib Typing

@[defaultTarget]
lean_exe yinlang {
  root := `Main
}
