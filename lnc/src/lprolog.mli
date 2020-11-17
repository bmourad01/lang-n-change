open Core_kernel

module Sigs: sig
  module Type: sig
    type t =
      | Var of string
      | Constructor of {
          name: string;
          args: t list;
        }

    val to_string: ?parens:bool -> t -> string
  end
  
  module Term: sig
    type t = {
        name: string; 
        args: Type.t list;
        typ: Type.t;
      }

    val to_string: t -> string
  end

  module Prop: sig
    type t = {
        name: string;
        args: Type.t list;
      }

    val to_string: t -> string
  end

  type t = {
      kinds: int String.Map.t;
      terms: Term.t String.Map.t;
      props: Prop.t String.Map.t;
    }

  val to_string: t -> string
end

module Term: sig
  type t =
    | Var of string
    | Str of string
    | Strcat of t * t
    | Constructor of {
        name: string;
        args: t list;
      }
    | Cons of t * t

  val to_string: t -> string
end

module Prop: sig
  type t =
    | Not of t
    | Eq of Term.t * Term.t
    | Prop of {
        name: string;
        args: Term.t list;
      }

  val to_string: t -> string
end

module Rule: sig
  type t = {
      name: string;
      premises: Prop.t list;
      conclusion: Prop.t;
    }

  val to_string: t -> string
end

type t = {
    sigs: Sigs.t;
    rules: Rule.t String.Map.t;
  }

val of_language: Language.t -> t
