import Lake
open Lake DSL

package «charleston-lean-meetup» where
  -- add package configuration options here

lean_lib «CharlestonLeanMeetup» where
  -- add library configuration options here

@[default_target]
lean_exe «charleston-lean-meetup» where
  root := `Main
