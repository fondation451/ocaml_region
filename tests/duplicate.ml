let rgn0 = newrgn () in
let rgn1 = newrgn () in
let rgn2 = newrgn () in
let rgn3 = newrgn () in
let rgn4 = newrgn () in

aliasrgn rgn1 in

let rec duplicate xs r r1 r2 =
  if xs = Nil @ rgn1 then
    (Nil @ r1, Nil @ r2) @ r
  else begin
    let dup = duplicate (tl xs) r r1 r2 in
    (Cons (hd xs) (fst dup) @ r1, Cons (hd xs) (snd dup) @ r2) @ r
  end
@
rgn0
in

let l = Cons 4 (Cons 5 (Cons 6 (Nil @ rgn1) @ rgn1) @ rgn1) @ rgn1 in

aliasrgn rgn2 in
aliasrgn rgn3 in
aliasrgn rgn4 in
duplicate l rgn2 rgn3 rgn4
