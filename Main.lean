import «CharlestonLeanMeetup»
open notes20240813

def main (args : List String) : IO UInt32 := do
  IO.println s!"list:   {args}"
  IO.println s!"vector: {list_to_vector args}"
  IO.println s!"array: {Array.mk args}"
  pure 0
