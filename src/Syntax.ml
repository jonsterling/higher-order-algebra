(* module Proxy = *)
(* struct *)
(*   type 'x t = P *)
(* end *)

module Nat =
struct
  type z = [`Z]
  type 'n s = [`S of 'n]
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
    | Z : ('m, 'm) t
    | S : ('m, 'n) t -> ('m, 'n Nat.s) t
  type 'x zero = ('x, 'x) t
  type 'x one  = ('x, 'x Nat.s) t
end

module Var = struct
  type ('m, 'n) t = ('m Nat.s, 'n) Ctx.t
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
    type (_,_) op =
      | Ax : ([`Ax], ni) op
      | Lm : ([`Lm], ('x Ctx.one, ni) co) op
      | Ap : ([`Ap], ('x Ctx.zero, ('x Ctx.zero, ni) co) co) op
    include Sign.S
      with type ('f, 'valences) op := ('f, 'valences) op
  end
  include (module type of Sign.Make(Sigma))

  type 'z clo = ('z, 'z) tm

  val v : ('m, 'n) Var.t -> ('m, 'n) tm
  val ax : ('m, 'n) tm
  val lm : ('m, 'n Nat.s) tm -> ('m, 'n) tm
  val ( *@ ) : ('m, 'n) tm -> ('m, 'n) tm -> ('m, 'n) tm
end =
struct
  module Sigma =
  struct
    open List
    type (_,_) op =
      | Ax : ([`Ax], unit) op
      | Lm : ([`Lm], ('x Ctx.one, ni) co) op
      | Ap : ([`Ap], ('x Ctx.zero, ('x Ctx.zero, ni) co) co) op
  end
  include Sign.Make(Sigma)

  type 'x clo = ('x, 'x) tm

  let v n = V n
  let ax = O (Sigma.Ax, N)
  let lm e = O (Sigma.Lm, C (e, N))
  let ( *@ ) e0 e1 = O (Sigma.Ap, C (e0, C (e1, N)))
end

module Test =
struct
  open Ctx
  open Lambda
  open List
  open Sigma

  let omega () : 'x Lambda.clo =
    lm (v Z *@ v Z) *@ lm (v Z *@ v Z)
end
