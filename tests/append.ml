(*
  Nicolas ASSOUAD

  Test function for memory consumption analysis
  Append

*)

let rgn1 = newrgn () in
let rgn2 = newrgn () in
begin
  aliasrgn rgn1 in
  aliasrgn rgn2 in

  let rgn3 = newrgn () in

  let rec append l1 l2 rgn =
    if l1 = Nil @ rgn3 then
      l2
    else
      Cons (hd l1) (append (tl l1) l2 rgn) @ rgn
  @
    rgn1
  in

  let l1 = Cons 1 (Cons 2 (Cons 3 (Nil @ rgn1) @ rgn1) @ rgn1) @ rgn1 in
  let l2 = Cons 4 (Cons 5 (Cons 6 (Nil @ rgn2) @ rgn2) @ rgn2) @ rgn2 in

  append l1 l2 rgn2;
  freergn rgn1
end
