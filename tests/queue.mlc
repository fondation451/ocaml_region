(*
  Nicolas ASSOUAD

  Test function for memory consumption analysis
  Queue

*)

let rgn0 = newrgn () in
let rgn1 = newrgn () in
aliasrgn rgn0 in
aliasrgn rgn1 in

let rec push q v r =
  Cons v q @ r
@
  rgn1
in

let rec pop q r =
  (hd q, tl q) @ r
@
  rgn1
in

let q = Nil @ rgn0 in
let q = push q 1 rgn0 in
let q = push q 2 rgn0 in
let q = push q 3 rgn0 in
let q = push q 4 rgn0 in
let q = push q 5 rgn0 in
let q = push q 6 rgn0 in
let q = push q 7 rgn0 in
let q = push q 8 rgn0 in
let q = push q 9 rgn0 in
let q = push q 10 rgn0 in

let tmp = pop q rgn1 in
let v = fst tmp in
let q = snd tmp in
let tmp = pop q rgn1 in
let v = fst tmp in
let q = snd tmp in
let tmp = pop q rgn1 in
let v = fst tmp in
let q = snd tmp in
()

