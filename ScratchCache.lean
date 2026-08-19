inductive E (C B X : Type) where
  | public
  | primitiveCall (point : C × B)
  | inner (input : X) (state : C) (pathPrefix : List B)
      (block : B) (rest : List B)
  | outer (input : X) (embedded state : C) (pathPrefix : List B)
      (block : B) (rest : List B)
  | done
deriving DecidableEq
