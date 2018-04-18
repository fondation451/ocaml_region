(*
  Nicolas ASSOUAD

  Test function for memory consumption analysis
  Append

*)

let rgn0 = newrgn () in
let rgn1 = newrgn () in
begin
  aliasrgn rgn0 in
  aliasrgn rgn1 in

  let rgn2 = newrgn () in

  let rec append l1 l2 rgn =
    if l1 = Nil @ rgn0 then
      l2
    else
      Cons (hd l1) (append (tl l1) l2 rgn) @ rgn
  @
    rgn1
  in

  let l1 = Cons 1 (Cons 2 (Cons 3 (Nil @ rgn0) @ rgn0) @ rgn0) @ rgn0 in
  let l2 = Cons 4 (Cons 5 (Cons 6 (Nil @ rgn1) @ rgn1) @ rgn1) @ rgn1 in

  append l1 l2 rgn1;
  freergn rgn0
end
