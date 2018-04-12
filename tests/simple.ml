(*
  Nicolas ASSOUAD

  Simple test

*)

let r1 = newrgn () in
let r2 = newrgn () in
begin
  aliasrgn r1 in
  let rec g x = x @ r2 in
  let rec f x = g x @ r1 in
  f;
  freergn r1;
  freergn r2
end
