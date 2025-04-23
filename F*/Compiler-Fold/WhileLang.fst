module WhileLang

open FStar.Map

type var = string



// Arithmetic expressions

type exp =
  | EConst : int -> exp
  | EVar : var -> exp
  | EAdd : exp -> exp -> exp
  | ESub : exp -> exp -> exp



// Boolean expressions

type bexp =
  | BConst : bool -> bexp
  | BEq : exp -> exp -> bexp
  | BLt : exp -> exp -> bexp
  | BGt : exp -> exp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp
  | BNot : bexp -> bexp



// Commands

type command =
  | Skip
  | Assign : var -> exp -> command
  | Seq : command -> command -> command
  | If : bexp -> command -> command -> command
  | While : bexp -> command -> nat -> command

type state = Map.t var int



// Evaluation functions

val eval_exp: state -> exp -> Tot int

let rec eval_exp s e =
  match e with
  | EConst n -> n
  | EVar x -> Map.sel s x
  | EAdd e1 e2 -> eval_exp s e1 + eval_exp s e2
  | ESub e1 e2 -> eval_exp s e1 - eval_exp s e2

val eval_bexp: state -> bexp -> Tot bool

let rec eval_bexp s b =
  match b with
  | BConst v -> v
  | BEq e1 e2 -> eval_exp s e1 = eval_exp s e2
  | BLt e1 e2 -> eval_exp s e1 < eval_exp s e2
  | BGt e1 e2 -> eval_exp s e1 > eval_exp s e2
  | BAnd b1 b2 -> eval_bexp s b1 && eval_bexp s b2
  | BOr b1 b2 -> eval_bexp s b1 || eval_bexp s b2
  | BNot b1 -> not (eval_bexp s b1)

let max (a b: nat) : nat = if a > b then a else b

let rec size (c: command) : nat =
  match c with
  | Skip -> 1
  | Assign _ _ -> 1
  | Seq c1 c2 -> 1 + size c1 + size c2
  | If _ c1 c2 -> 1 + max (size c1) (size c2)
  | While _ body n -> 1 + size body + n



// Command evaluation

let rec exec (s: state) (c: command) : Tot state (decreases (size c)) =
  match c with
  | Skip -> s
  | Assign x e -> Map.upd s x (eval_exp s e)
  | Seq c1 c2 -> exec (exec s c1) c2
  | If b c1 c2 -> if eval_bexp s b then exec s c1 else exec s c2
  | While b body n ->
    if n = 0 then s else if eval_bexp s b then exec (exec s body) (While b body (n - 1)) else s



// Constant folding for exp

let rec fold_constants_exp (e: exp) : exp =
  match e with
  | EAdd (EConst n1) (EConst n2) -> EConst (n1 + n2)
  | ESub (EConst n1) (EConst n2) -> EConst (n1 - n2)
  | EAdd e1 e2 -> EAdd (fold_constants_exp e1) (fold_constants_exp e2)
  | ESub e1 e2 -> ESub (fold_constants_exp e1) (fold_constants_exp e2)
  | _ -> e

val const_fold: command -> command

let rec const_fold c =
  match c with
  | Skip -> Skip
  | Assign x e -> Assign x (fold_constants_exp e)
  | Seq c1 c2 -> Seq (const_fold c1) (const_fold c2)
  | While b body n -> While b (const_fold body) n
  | If b c1 c2 ->
    (match b with
    | BConst true -> const_fold c1
    | BConst false -> const_fold c2
    | _ -> If b (const_fold c1) (const_fold c2))
  | _ -> c

val const_fold_preserves_semantics (c: command) (s: state)
    : Lemma (requires True) (ensures (exec s c == exec s (const_fold c)))

val fold_constants_exp_preserves (e: exp) (s: state)
    : Lemma (eval_exp s e == eval_exp s (fold_constants_exp e))
      [SMTPat (eval_exp s (fold_constants_exp e))]

let rec fold_constants_exp_preserves (e: exp) (s: state)
    : Lemma (eval_exp s e == eval_exp s (fold_constants_exp e))
      [SMTPat (eval_exp s (fold_constants_exp e))] =
  match e with
  | EConst n -> ()
  | EVar x -> ()
  | EAdd e1 e2 ->
    fold_constants_exp_preserves e1 s;
    fold_constants_exp_preserves e2 s;
    (match fold_constants_exp e with
      | EConst n -> () // folded case like EAdd (EConst 2) (EConst 3)
      | EAdd e1' e2' -> () // normal recursive case, semantics still preserved
      | _ ->
        // shouldn't happen
        assert False)
  | ESub e1 e2 ->
    fold_constants_exp_preserves e1 s;
    fold_constants_exp_preserves e2 s;
    match fold_constants_exp e with
    | EConst n -> ()
    | ESub e1' e2' -> ()
    | _ -> assert False

#push-options "--fuel 200"

let rec const_fold_preserves_semantics c s
    : Lemma (ensures exec s c == exec s (const_fold c)) (decreases size c) =
  match c with
  | Skip -> ()
  | Assign x e ->
    assert (eval_exp s e == eval_exp s (fold_constants_exp e));
    ()
  | Seq c1 c2 ->
    const_fold_preserves_semantics c1 s;
    const_fold_preserves_semantics c2 (exec s c1);
    ()
  | If b c1 c2 ->
    (match b with
      | BConst true -> const_fold_preserves_semantics c1 s
      | BConst false -> const_fold_preserves_semantics c2 s
      | _ ->
        assert (eval_bexp s b == eval_bexp s b);
        if eval_bexp s b
        then const_fold_preserves_semantics c1 s
        else const_fold_preserves_semantics c2 s)
  | While b body n ->
    if n = 0
    then ()
    else
      let n' = n - 1 in
      assert (n' >= 0); // Now we know n' : int is non-negative
      const_fold_preserves_semantics body s;
      assert (n' < n); // Prove that n' is strictly smaller than n
      const_fold_preserves_semantics (While b body (n')) (exec s body)



// x := 3 + 4

let test1 = Assign "x" (EAdd (EConst 3) (EConst 4))

let reduced1 = const_fold test1

let expected1 = Assign "x" (EConst 7)

let _ = assert (reduced1 == expected1)



// while x > 0 do x := x - 1

let test2 = While (BGt (EVar "x") (EConst 0)) (Assign "x" (ESub (EConst 3) (EConst 1))) 10

let reduced2 = const_fold test2

let expected2 = While (BGt (EVar "x") (EConst 0)) (Assign "x" (EConst 2)) 10

let _ = assert (reduced2 == expected2)



// if x < 10 then y := 1 else y := 2

let test3 =
  If (BLt (EVar "x") (EConst 10)) (Assign "y" (EAdd (EConst 3) (EConst 2))) (Assign "y" (EConst 2))

let reduced3 = const_fold test3

let expected3 = If (BLt (EVar "x") (EConst 10)) (Assign "y" (EConst 5)) (Assign "y" (EConst 2))

let _ = assert (reduced3 == expected3)