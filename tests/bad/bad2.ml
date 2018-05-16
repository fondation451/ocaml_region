(*
  Nicolas ASSOUAD

  Bad Typing Example 2

*)

let rgn0 = newrgn () in
let rgn1 = newrgn () in
let rgn2 = newrgn () in

let rec insert_pair l x r1 r2 =
  Cons ((x, x) @ r1) l @ r2
@
rgn0
in

let l = [(6, 4) @ rgn1] @ rgn2 in

aliasrgn rgn1 in

begin

  insert_pair l 2 rgn1 rgn2;
  ()
end
