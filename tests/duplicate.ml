let rgn0 = newrgn () in
let rgn1 = newrgn () in
let rgn2 = newrgn () in
let rgn3 = newrgn () in
let rgn4 = newrgn () in

aliasrgn rgn1 in

let rec duplicate xs r r1 r2 =
  { r1: size(xs) -> 0 ; r2: size(xs) -> 0 }
  match xs with
  |Nil -> (Nil @ r1, Nil @ r2) @ r
  |Cons h t -> begin
    let dup = duplicate t r r1 r2 in
    (Cons h (fst dup) @ r1, Cons h (snd dup) @ r2) @ r
  end
@
rgn0
in

let l = [4 ; 5 ; 6] @ rgn1 in

aliasrgn rgn2 in
aliasrgn rgn3 in
aliasrgn rgn4 in
begin
  duplicate l rgn2 rgn3 rgn4;
  let dump = [4 ; 5 ; 6] @ rgn1 in
  duplicate l rgn2 rgn3 rgn4;
  ()
end
