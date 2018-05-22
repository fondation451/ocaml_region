(*
  Nicolas ASSOUAD

  Test function for memory consumption analysis
  Filter (list)

*)

let rgn1 = newrgn () in
let rgn2 = newrgn () in
aliasrgn rgn1 in
aliasrgn rgn2 in

let rec filter p l out rgn =
  if l = Nil @ rgn1 then
    out
  else
    if p (hd l) then
      filter p (tl l) (Cons (hd l) out @ rgn) rgn
    else
      filter p (tl l) out rgn
@
  rgn1
in

let l = Cons 1 (Cons 2 (Cons 3 (Nil @ rgn1) @ rgn1) @ rgn1) @ rgn1 in
let rec even n = true @ rgn1 in

filter even l (Nil @ rgn2) rgn2
