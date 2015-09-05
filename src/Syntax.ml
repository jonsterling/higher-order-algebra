(* module Proxy = *)
(* struct *)
(*   type 'x t = P *)
(* end *)

module Nat =
struct
  type z = Z
  type 'n s = S
end

module List =
struct
  type ni = unit
  type ('x, 'xs) co = 'x * 'xs
  (* type _ t = *)
  (*   | Z : ni t *)
  (*   | S : 'x Proxy.t * 'xs t -> ('x, 'xs) co t *)
end

module Ctx =
struct
  type (_,_) t =
    | Z : ('m, 'n) t
    | S : ('m, 'n) t -> ('m, 'n Nat.s) t
  type 'x zero = ('x, 'x) t
  type 'x one  = ('x, 'x Nat.s) t
end

module Var = struct
  type (_,_) t =
    | Z : ('m, 'n Nat.s) t
    | S : ('m, 'n) t -> ('m, 'n Nat.s) t
end

module Sign = struct
  module type S =
  sig
    type ('f, 'valences) op
  end

  module rec Spine : functor (Sigma : S) ->
  sig
    type (_,_,_,_) sp =
      | N : ('f, List.ni, 'm, 'n) sp
      | C : ('m, 'o) Term(Sigma).tm * ('f, 'gs, 'm, 'n) sp -> ('f, (('n, 'o) Ctx.t, 'gs) List.co, 'm, 'n) sp
  end = functor (Sigma : S) ->
  struct
    type (_,_,_,_) sp =
      | N : ('f, List.ni, 'm, 'n) sp
      | C : ('m, 'o) Term(Sigma).tm * ('f, 'gs, 'm, 'n) sp -> ('f, (('n, 'o) Ctx.t, 'gs) List.co, 'm, 'n) sp
  end

  and Term : functor (Sigma : S) ->
  sig
    type (_,_) tm =
      | V : ('m, 'n) Var.t -> ('m, 'n) tm
      | O : ('f, 'arity) Sigma.op * ('f, 'arity, 'm, 'n) Spine(Sigma).sp -> ('m, 'n) tm
  end = functor (Sigma : S) ->
  struct
    type (_,_) tm =
      | V : ('m, 'n) Var.t -> ('m, 'n) tm
      | O : ('f, 'arity) Sigma.op * ('f, 'arity, 'm, 'n) Spine(Sigma).sp -> ('m, 'n) tm
  end

  module Make : functor (Sigma : S) ->
  sig
    include (module type of Spine(Sigma))
    include (module type of Term (Sigma))
  end = functor (Sigma : S) ->
  struct
    include Spine(Sigma)
    include Term (Sigma)
  end
end

module Lambda :
sig
  module Sigma :
  sig
    open List
    type (_,_) depth =
      | DZ : ('m, 'm) depth
      | DS : ('m, 'n) depth -> ('m, 'n Nat.s) depth
    type (_,_) op = ..
    type (_,_) op += Ax : ([`Ax], ni) op
    type (_,_) op += Lm : ('m, 'n) depth -> ([`Lm], (('m, 'n) Ctx.t, ni) co) op
    type (_,_) op += Ap : ([`Ap], ('x Ctx.zero, ('x Ctx.zero, ni) co) co) op
    include Sign.S
      with type ('f, 'valences) op := ('f, 'valences) op
  end
  include (module type of Sign.Make(Sigma))

  type 'n t = (Nat.z, 'n) tm

  val dz : ('m, 'm) Sigma.depth
  val ds : ('m, 'n) Sigma.depth -> ('m, 'n Nat.s) Sigma.depth
  val z : ('m, 'n Nat.s) Var.t
  val s : ('m, 'n) Var.t -> ('m, 'n Nat.s) Var.t
  val v : ('m, 'n) Var.t -> ('m, 'n) tm
  val ax : ('m, 'n) tm
  val ln : ('n, 'o) Sigma.depth -> ('m, 'o) tm -> ('m, 'n) tm
  val l1 : ('m, 'n Nat.s) tm -> ('m, 'n) tm
  val ( *@ ) : ('m, 'n) tm -> ('m, 'n) tm -> ('m, 'n) tm
end =
struct
  module Sigma =
  struct
    open List
    type (_,_) depth =
      | DZ : ('m, 'm) depth
      | DS : ('m, 'n) depth -> ('m, 'n Nat.s) depth
    type (_,_) op = ..
    type (_,_) op += Ax : ([`Ax], ni) op
    type (_,_) op += Lm : ('m, 'n) depth -> ([`Lm], (('m, 'n) Ctx.t, ni) co) op
    type (_,_) op += Ap : ([`Ap], ('x Ctx.zero, ('x Ctx.zero, ni) co) co) op
  end
  include Sign.Make(Sigma)

  type 'n t = (Nat.z, 'n) tm

  let dz = Sigma.DZ
  let ds n = Sigma.DS n
  let z = Var.Z
  let s n = Var.S n
  let v n = V n
  let ax = O (Sigma.Ax, N)
  let ln n e = O (Sigma.Lm n, C (e, N))
  let l1 e = ln (ds dz) e
  let ( *@ ) e0 e1 = O (Sigma.Ap, C (e0, C (e1, N)))
end

module Test =
struct
  open Lambda
  open List
  open Sigma
  open Var

  let omega () : Nat.z Lambda.t =
    l1 (v z *@ v z) *@ l1 (v z *@ v z)

  let test0 () : Nat.z Lambda.t =
    ln (ds @@ ds @@ ds @@ dz) (v @@ s @@ s @@ z)
end
