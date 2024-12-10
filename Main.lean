import Std
open Std (HashMap)

#check compare
#check HashMap
#check HashMap.alter
#check HashMap.empty
#check List.drop
#check List.filterMap
#check List.flatten
#check List.foldl
#check List.map
#check List.mergeSort
#check List.range
#check List.take
#check Option.none
#check Option.some
#check Ordering
#check (Ordering.eq, Ordering.lt, Ordering.gt)
#check String.mk
#check String.splitOn
#check String.toList
#check String.toNat!


def day_1_a (lines : List String) : Nat := sorry


def main (args : List String) : IO UInt32 :=
  match args with
  | [] => do
      IO.println "pass a filename"
      pure 1
  | filename::_ => do
      let ans <- (day_1_a ∘ Array.toList) <$> IO.FS.lines ⟨filename⟩
      IO.println ans
      pure 0
