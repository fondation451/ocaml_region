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

  let rec append l1 l2 rgn =
    { rgn: size(l1) -> 0; rgn1: 0 -> 0 }
    if l1 = Nil @ rgn0 then
      l2
    else
      Cons (hd l1) (append (tl l1) l2 rgn) @ rgn
  @
    rgn1
  in

  let l1 = [0 ; 1 ; 2 ; 3] @ rgn0 in
  let l2 = [4 ; 5 ; 6] @ rgn1 in

  append l1 l2 rgn1;
  freergn rgn0
end
