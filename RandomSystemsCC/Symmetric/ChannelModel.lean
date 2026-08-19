/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedFinite

/-!
# Shared channel interfaces for symmetric constructions

The symmetric-construction suite uses the paper's Alice--Bob--Eve interface
shape.  Concrete constructions define their own typed signature universes and
resource laws; this file fixes only the common interface names and the
external send/receive operations needed by their final channel resources.
-/

namespace RandomSystemsCC.Symmetric

universe u

/-- The three interfaces of the channel constructions. -/
inductive Interface
  | alice
  | bob
  | eve
  deriving DecidableEq, Fintype

/-- Alice submits one message to a channel. -/
inductive SenderIn (M : Type u) : Type u
  | send (message : M)
  deriving DecidableEq

/-- Bob requests the channel's delivered message. -/
inductive ReceiverIn (M : Type u) : Type u
  | receive
  deriving DecidableEq

/-- Eve requests the view exposed by a channel resource. -/
inductive EveIn (M : Type u) : Type u
  | observe
  deriving DecidableEq

/-- A write was accepted.  The type parameter keeps this answer in the same
universe as the construction's message type. -/
inductive Ack (M : Type u) : Type u
  | ack
  deriving DecidableEq

/-- The query accepted by an availability-blocked adversarial port. -/
inductive BlockedIn (M : Type u) : Type u
  | query
  deriving DecidableEq

/-- The answer returned by an availability-blocked adversarial port. -/
inductive BlockedOut (M : Type u) : Type u
  | blocked
  deriving DecidableEq

end RandomSystemsCC.Symmetric
