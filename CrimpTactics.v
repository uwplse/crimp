Require Import Query Imp.

Ltac break_match :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?
    | [ H : context [ match ?X with _ => _ end ] |- _] => destruct X eqn:?
  end.


Ltac inv H := inversion H; subst; clear H.


Ltac unfold_all := repeat match goal with 
                  | [ |- runImp' _ _ _ = _ ] => unfold runImp'; [repeat break_match; try discriminate]
                  | [H: runImp' _ _ _ = _ |- _ ] => unfold runImp' in H; [repeat break_match; try discriminate]
                  | [H: runQuery _ _ _ = _ |- _ ] => unfold runQuery in H; [repeat break_match; try discriminate]
                  | H: project _ _ = _ |- _ => unfold project in H                 
                  | [H: runStatement _ _ _ _ _ = _ |- _ ] => unfold runStatement in H; [repeat break_match; try discriminate]
                end.


Ltac inv_somes := repeat match goal with
                           | [ H: Some _ = Some _ |- _ ] => inv H
                         end.


Ltac massage_ihr1 := match goal with
                              | H:context [ forall r2 _, runQuery _ _ _ = _ -> runImp' _ _ _ = _ ] |- _  => specialize (H r2); unfold runQuery in H
                     end.
