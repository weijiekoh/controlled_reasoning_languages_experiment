def ok (n : Nat) (f : Nat → Nat) : Bool := Id.run do
  let mut S : Array Nat := Array.replicate (2*n+2) 3
  for i in [1:n+1] do
    for j in [1:n+1] do
      if f i != f j then
        let k := 3 - f i - f j
        if S[i+j]! == 3 then S := S.set! (i+j) k
        else if S[i+j]! != k then return false
  return true
def go (n : Nat) : List String := Id.run do
  let mut r := []
  for m in [0:3^n] do
    let f := fun i => (m / 3^(i-1)) % 3
    let fs := (List.range n).map (fun i => f (i+1))
    if fs.contains 0 && fs.contains 1 && fs.contains 2 && ok n f then
      r := (String.join (fs.map toString)) :: r
  return r
#eval (go 10).length
#eval go 10
#eval (go 12).length
