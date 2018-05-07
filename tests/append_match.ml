(*
  Nicolas ASSOUAD

  Test function for memory consumption analysis
  Append with match

*)

let rgn0 = newrgn () in
let rgn1 = newrgn () in
begin
  aliasrgn rgn0 in
  aliasrgn rgn1 in

  let rec append l1 l2 rgn =
    { rgn: size(l1) -> 0; rgn1: 0 -> 0 }
    match l1 with
    |Nil -> l2
    |Cons x xs -> Cons x (append xs l2 rgn) @ rgn
  @
    rgn1
  in

  let l1 = [0 ; 1 ; 2 ; 3] @ rgn0 in
  let l2 = [4 ; 5 ; 6] @ rgn1 in
(*
  let l1 = Cons 0 (Cons 1 (Cons 2 (Cons 3 (Nil @ rgn0) @ rgn0) @ rgn0) @ rgn0) @ rgn0 in
  let l2 = Cons 4 (Cons 5 (Cons 6 (Nil @ rgn1) @ rgn1) @ rgn1) @ rgn1 in
*)
  append l1 l2 rgn1;
  freergn rgn0
end
