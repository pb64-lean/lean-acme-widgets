module

public import AcmeLean.widgets
public import AcmeValid.widgets
public import Acme.Auth
public import Acme.Repo
import all AcmeLean.widgets

public section

namespace Acme
namespace Model

open acme.v1

/-!
Pure in-memory model of the widget service's mutating surface. Commands are
exactly the repository capabilities (`Acme.Repo.Authorized*`) — the model
consumes the same evidence the SQL repository does — so policy-preservation
facts about `applyCommand` are statements about what any store driven by
authorized commands can look like: creates insert rows owned by the
authenticated principal, updates rewrite only rows owned by the
authenticated principal, deletes remove only the (id, owner) pair that the
delete policy tied to the principal (owner or admin override).
-/

/-- In-memory store: assigned-id → widget associations plus the next fresh id. -/
structure Store where
  widgets : List (UInt64 × Widget) := []
  nextId : UInt64 := 1

/-- The mutating commands, carrying capabilities — an unauthorized command is
unrepresentable. -/
inductive Command where
  | create (cap : Repo.AuthorizedCreate)
  | update (cap : Repo.AuthorizedUpdate)
  | delete (cap : Repo.AuthorizedDelete)

/-- Mirror of the repository's SQL semantics: insert with a fresh id; update
by (id, owner); delete by (id, owner). -/
def applyCommand (s : Store) : Command → Store
  | .create cap =>
    let w := cap.request.widget.toBase
    { widgets := (s.nextId, { w with id := s.nextId }) :: s.widgets,
      nextId := s.nextId + 1 }
  | .update cap =>
    let w := cap.request.widget.toBase
    { s with widgets := s.widgets.map fun entry =>
        if entry.1 == w.id && entry.2.owner_id == w.owner_id then (entry.1, w)
        else entry }
  | .delete cap =>
    { s with widgets := s.widgets.filter fun entry =>
        !(entry.1 == cap.request.widget_id.val
          && entry.2.owner_id == cap.request.user_id.val) }

/-- Creation inserts a row owned by the *authenticated* principal. -/
theorem create_inserts_owned (s : Store) (cap : Repo.AuthorizedCreate) :
    ∃ w, (applyCommand s (.create cap)).widgets.head? = some (s.nextId, w) ∧
      w.owner_id = cap.principal.id := by
  refine ⟨{ cap.request.widget.toBase with id := s.nextId }, rfl, ?_⟩
  exact cap.owner_eq

/-- Updates rewrite only rows owned by the authenticated principal: any row
with a different owner is preserved verbatim. -/
theorem update_preserves_foreign (s : Store) (cap : Repo.AuthorizedUpdate)
    (entry : UInt64 × Widget) (hin : entry ∈ s.widgets)
    (howner : entry.2.owner_id ≠ cap.principal.id) :
    entry ∈ (applyCommand s (.update cap)).widgets := by
  have hne : entry.2.owner_id ≠ cap.request.widget.toBase.owner_id := by
    rw [cap.owner_eq]; exact howner
  have hfix : (if entry.1 == cap.request.widget.toBase.id
        && entry.2.owner_id == cap.request.widget.toBase.owner_id
      then (entry.1, cap.request.widget.toBase) else entry) = entry := by
    rw [if_neg]
    intro hcond
    exact hne (beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hcond).2)
  show entry ∈ s.widgets.map _
  exact List.mem_map.mpr ⟨entry, hin, hfix⟩

/-- Deletion removes only the row the policy authorized: a row that
disappears carried exactly the named (widget_id, owner) pair — and
`cap.self_or_admin` ties that owner to the principal or an admin override. -/
theorem delete_removes_named_only (s : Store) (cap : Repo.AuthorizedDelete)
    (entry : UInt64 × Widget) (hin : entry ∈ s.widgets)
    (hout : entry ∉ (applyCommand s (.delete cap)).widgets) :
    entry.1 = cap.request.widget_id.val
      ∧ entry.2.owner_id = cap.request.user_id.val := by
  by_cases hp : (!(entry.1 == cap.request.widget_id.val
      && entry.2.owner_id == cap.request.user_id.val)) = true
  · exact absurd (List.mem_filter.mpr ⟨hin, hp⟩) hout
  · have hcond : (entry.1 == cap.request.widget_id.val
        && entry.2.owner_id == cap.request.user_id.val) = true := by
      cases hb : (entry.1 == cap.request.widget_id.val
          && entry.2.owner_id == cap.request.user_id.val) with
      | true => rfl
      | false => exact absurd (by rw [hb]; rfl) hp
    have := (Bool.and_eq_true _ _).mp hcond
    exact ⟨beq_iff_eq.mp this.1, beq_iff_eq.mp this.2⟩

/-- The store invariant "every row's owner was an authenticated identity
(positive id)" is preserved by every authorized command. -/
def WellOwned (s : Store) : Prop :=
  ∀ entry ∈ s.widgets, 0 < (entry : UInt64 × Widget).2.owner_id

theorem applyCommand_wellOwned (s : Store) (c : Command) (h : WellOwned s) :
    WellOwned (applyCommand s c) := by
  cases c with
  | create cap =>
    intro entry hmem
    cases hmem with
    | head => exact cap.owner_eq ▸ cap.principal.id_pos
    | tail _ hmem => exact h entry hmem
  | update cap =>
    intro entry hmem
    obtain ⟨orig, horig, hmap⟩ := List.mem_map.mp hmem
    by_cases hcond : (orig.1 == cap.request.widget.toBase.id
        && orig.2.owner_id == cap.request.widget.toBase.owner_id) = true
    · rw [if_pos hcond] at hmap
      subst hmap
      exact cap.owner_eq ▸ cap.principal.id_pos
    · rw [if_neg hcond] at hmap
      subst hmap
      exact h orig horig
  | delete cap =>
    intro entry hmem
    exact h entry (List.mem_filter.mp hmem).1

end Model
end Acme
