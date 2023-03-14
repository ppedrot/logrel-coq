(** * LogRel.GenericTyping: the generic interface of typing used to build the logical relation. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction DeclarativeTyping.

(** In order to factor the work, the logical relation is defined over a generic
notion of typing (and conversion),
and its properties are established given abstract properties
of this generic notion. This way, we can instantiate the logical relation multiple
times with different instances of this abstract notion of typing, gathering more
and more properties. *)

(**
More precisely, an instance consists of giving notions of 
- context well-formation [|- Γ]
- type well-formation [Γ |- A]
- term well-formation [Γ |- t : A]
- convertibility of types [Γ |- A ≅ B]
- convertibility of terms [Γ |- t ≅ u : A]
- neutral convertibility of terms [Γ |- m ~ n : A]
- (multi-step, weak-head) reduction of types [Γ |- A ⇒* B]
- (multi-step, weak-head) reduction of terms [Γ |- t ⇒* u : A]
*)

(** ** Generic definitions *)

(** These can be defined over typing and conversion in a generic way. *)

Section RedDefinitions.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  (** *** Bundling of a predicate with side-conditions *)

  Record TypeRedWhnf (Γ : context) (A B : term) : Type :=
    {
      tyred_whnf_red :> [ Γ |- A ⇒* B ] ;
      tyred_whnf_whnf :> whnf B
    }.

  Record TermRedWhnf (Γ : context) (A t u : term) : Type :=
    {
      tmred_whnf_red :> [ Γ |- t ⇒* u : A ] ;
      tmred_whnf_whnf :> whnf u
    }.

  Record TypeConvWf (Γ : context) (A B : term) : Type :=
    { 
      tyc_wf_l : [Γ |- A] ;
      tyc_wf_r : [Γ |- B] ;
      tyc_wf_conv :> [Γ |- A ≅ B]
    }.

  Record TermConvWf (Γ : context) (A t u : term) : Type :=
    {
      tmc_wf_l : [Γ |- t : A] ;
      tmc_wf_r : [Γ |- u : A] ;
      tmc_wf_conv :> [Γ |- t ≅ u : A]
    }.

  Record TypeRedWf (Γ : context) (A B : term) : Type := {
    tyr_wf_l : [Γ |- A];
    tyr_wf_r : [Γ |- B];
    tyr_wf_red :> [Γ |- A ⇒* B]
  }.

  Record TermRedWf (Γ : context) (A t u : term) : Type := {
    tmr_wf_l : [Γ |- t : A];
    tmr_wf_r : [Γ |- u : A];
    tmr_wf_red :> [Γ |- t ⇒* u : A]
  }.

  (** *** Lifting of typing and conversion to contexts and substitutions *)

  Inductive WellSubst (Γ : context) : context -> (nat -> term) -> Type :=
    | well_sempty (σ : nat -> term) : [Γ |-s σ : ε ]
    | well_scons (σ : nat -> term) (Δ : context) na A :
      [Γ |-s ↑ >> σ : Δ] -> [Γ |- σ var_zero : A[↑ >> σ]] ->
      [Γ |-s σ : Δ,, vass na A]
  where "[ Γ '|-s' σ : Δ ]" := (WellSubst Γ Δ σ).

  Inductive ConvSubst (Γ : context) : context -> (nat -> term) -> (nat -> term) -> Type :=
  | conv_sempty (σ τ : nat -> term) : [Γ |-s σ ≅ τ : ε ]
  | conv_scons (σ τ : nat -> term) (Δ : context) na A :
    [Γ |-s ↑ >> σ ≅ ↑ >> τ : Δ] -> [Γ |- σ var_zero ≅ τ var_zero: A[↑ >> σ]] ->
    [Γ |-s σ ≅ τ : Δ,, vass na A]
  where "[ Γ '|-s' σ ≅ τ : Δ ]" := (ConvSubst Γ Δ σ τ).

  Inductive ConvCtx : context -> context -> Type :=
  | conv_cempty : [ |- ε ≅ ε]
  | conv_ccons Γ na A Δ nb B : [ |- Γ ≅ Δ ] -> [Γ |- A ≅ B] -> [ |- Γ,, vass na A ≅ Δ,, vass nb B]
  where "[ |- Γ ≅ Δ ]" := (ConvCtx Γ Δ).

End RedDefinitions.

Notation "[ Γ |- A ↘ B ]" := (TypeRedWhnf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ↘ B ]" := (TypeRedWhnf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t ↘ u : A ]" := (TermRedWhnf Γ A t u) (only parsing ): typing_scope.
Notation "[ Γ |-[ ta  ] t ↘ u : A ]" := (TermRedWhnf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ |- A :≅: B ]" := (TypeConvWf Γ A B) (only parsing) : typing_scope.  
Notation "[ Γ |-[ ta  ] A :≅: B ]" := (TypeConvWf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t :≅: u : A ]" := (TermConvWf Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :≅: u : A ]" := (TermConvWf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ |- A :⇒*: B ]" := (TypeRedWf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A :⇒*: B ]" := (TypeRedWf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t :⇒*: u : A ]" := (TermRedWf Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :⇒*: u : A ]" := (TermRedWf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ '|-s' σ : A ]" := (WellSubst Γ A σ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ : A ]" := (WellSubst (ta := ta) Γ A σ) : typing_scope.
Notation "[ Γ '|-s' σ ≅ τ : A ]" := (ConvSubst Γ A σ τ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ ≅ τ : A ]" := (ConvSubst (ta := ta) Γ A σ τ) : typing_scope.
Notation "[ |- Γ ≅ Δ ]" := (ConvCtx Γ Δ) (only parsing) : typing_scope.
Notation "[ |-[ ta  ] Γ ≅ Δ ]" := (ConvCtx (ta := ta) Γ Δ) : typing_scope.

#[export] Hint Resolve
  Build_TypeRedWhnf Build_TermRedWhnf Build_TypeConvWf
  Build_TermConvWf Build_TypeRedWf Build_TermRedWf
  well_sempty well_scons conv_sempty conv_scons
  tyr_wf_l tyr_wf_r tyr_wf_red tmr_wf_l tmr_wf_r tmr_wf_red
  : gen_typing.

(* #[export] Hint Extern 1 =>
  match goal with
    | H : [ _ |- _ ▹h _ ] |- _ => destruct H
    |  H : [ _ |- _ ↘ _ ] |- _ => destruct H
    |  H : [ _ |- _ ↘ _ : _ ] |- _ => destruct H
    |  H : [ _ |- _ :≅: _ ] |- _ => destruct H
    |  H : [ _ |- _ :≅: _ : _] |- _ => destruct H
    |  H : [ _ |- _ :⇒*: _ ] |- _ => destruct H
    |  H : [ _ |- _ :⇒*: _ : _ ] |- _ => destruct H
  end
  : gen_typing. *)

(** ** Properties of the abstract interface *)

Section GenericTyping.

  Import DeclarativeTypingData.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta} `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!OneStepRedTerm ta} `{!RedTerm ta}.

  Class WfContextProperties :=
  {
    wfc_nil : [|- ε ] ;
    wfc_cons {Γ} na {A} : [|- Γ] -> [Γ |- A] -> [|- Γ,,vass na A];
    wfc_wft {Γ A} : [Γ |- A] -> [|- Γ];
    wfc_ty {Γ A t} : [Γ |- t : A] -> [|- Γ];
    wfc_convty {Γ A B} : [Γ |- A ≅ B] -> [|- Γ];
    wfc_convtm {Γ A t u} : [Γ |- t ≅ u : A] -> [|- Γ];
    wfc_redty {Γ A B} : [Γ |- A ⇒* B] -> [|- Γ];
    wfc_redtm {Γ A t u} : [Γ |- t ⇒* u : A] -> [|- Γ];
    wfc_sound {Γ} : [|- Γ] -> [|-[de] Γ]
  }.

  Class WfTypeProperties :=
  {
    wft_wk {Γ Δ A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A] -> [Δ |- A⟨ρ⟩] ;
    wft_sound {Γ A} : [Γ |- A] -> [Γ |-[de] A] ;
    wft_U {Γ} : 
      [ |- Γ ] ->
      [ Γ |- U ] ;
    wft_prod {Γ} {na : aname} {A B} : 
      [ Γ |- A ] -> 
      [Γ ,, (vass na A) |- B ] -> 
      [ Γ |- tProd na A B ] ;
    wft_term {Γ} {A} :
      [ Γ |- A : U ] -> 
      [ Γ |- A ] ;
  }.

  Class TypingProperties :=
  {
    ty_wk {Γ Δ t A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t : A] -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩] ;
    ty_sound {Γ A t} : [Γ |- t : A] -> [Γ |-[de] t : A] ;
    ty_var {Γ} {n decl} :
      [   |- Γ ] ->
      in_ctx Γ n decl ->
      [ Γ |- tRel n : decl.(decl_type) ] ;
    ty_prod {Γ} {na} {A B} :
        [ Γ |- A : U] -> 
        [Γ ,, (vass na A) |- B : U ] ->
        [ Γ |- tProd na A B : U ] ;
    ty_lam {Γ} {na} {A B t} :
        [ Γ |- A ] ->
        [ Γ ,, vass na A |- t : B ] -> 
        [ Γ |- tLambda na A t : tProd na A B] ;
    ty_app {Γ} {na} {f a A B} :
        [ Γ |- f : tProd na A B ] -> 
        [ Γ |- a : A ] -> 
        [ Γ |- tApp f a : B[a ..] ] ;
    ty_exp {Γ t A A'} : [Γ |- t : A'] -> [Γ |- A ⇒* A'] -> [Γ |- t : A] ;
    ty_conv {Γ t A A'} : [Γ |- t : A'] -> [Γ |- A' ≅ A] -> [Γ |- t : A] ;
  }.

  Class ConvTypeProperties :=
  {
    convty_term {Γ A B} : [Γ |- A ≅ B : U] -> [Γ |- A ≅ B] ;
    convty_equiv {Γ} :> PER (conv_type Γ) ;
    convty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A ≅ B] -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩] ;
    convty_sound {Γ A B} : [Γ |- A ≅ B] -> [Γ |-[de] A ≅ B] ;
    convty_exp {Γ A A' B B'} :
      [Γ |- A ⇒* A'] -> [Γ |- B ⇒* B'] ->
      [Γ |- A' ≅ B'] -> [Γ |- A ≅ B] ;
    convty_uni {Γ} :
      [|- Γ] -> [Γ |- U ≅ U] ;
    convty_prod {Γ na na' A A' B B'} :
      eq_binder_annot na na' -> [Γ |- A] ->
      [Γ |- A ≅ A'] -> [Γ,, vass na A |- B ≅ B'] ->
      [Γ |- tProd na A B ≅ tProd na' A' B'] ;
  }.

  Class ConvTermProperties :=
  {
    convtm_equiv {Γ A} :> PER (conv_term Γ A) ;
    convtm_conv {Γ t u A A'} : [Γ |- t ≅ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ≅ u : A'] ;
    convtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ≅ u : A] -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩] ;
    convtm_sound {Γ A t u} : [Γ |- t ≅ u : A] -> [Γ |-[de] t ≅ u : A] ;
    convtm_exp {Γ A A' t t' u u'} :
      [Γ |- A ⇒* A'] -> [Γ |- t ⇒* t' : A'] -> [Γ |- u ⇒* u' : A'] ->
      [Γ |- t' ≅ u' : A'] -> [Γ |- t ≅ u : A] ;
    convtm_convneu {Γ n n' A} :
      [Γ |- n ~ n' : A] -> [Γ |- n ≅ n' : A] ;
    convtm_prod {Γ na na' A A' B B'} :
      eq_binder_annot na na' -> [Γ |- A : U] ->
      [Γ |- A ≅ A' : U] -> [Γ,, vass na A |- B ≅ B' : U] ->
      [Γ |- tProd na A B ≅ tProd na' A' B' : U] ;
    convtm_eta {Γ na f g A B} :
      [ Γ |- A ] ->
      [ Γ |- f : tProd na A B ] ->
      isFun f ->
      [ Γ |- g : tProd na A B ] ->
      isFun g ->
      [ Γ ,, vass na A |- eta_expand f ≅ eta_expand g : B ] ->
      [ Γ |- f ≅ g : tProd na A B ] ;
  }.

  Class ConvNeuProperties :=
  {
    convneu_equiv {Γ A} :> PER (conv_neu_conv Γ A) ;
    convneu_conv {Γ t u A A'} : [Γ |- t ~ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ~ u : A'] ;
    convneu_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ~ u : A] -> [Δ |- t⟨ρ⟩ ~ u⟨ρ⟩ : A⟨ρ⟩] ;
    convneu_sound {Γ A t u} : [Γ |- t ~ u : A] -> [Γ |-[de] t ~ u : A] ;
    convneu_var {Γ n A} :
      [Γ |- tRel n : A] -> [Γ |- tRel n ~ tRel n : A] ;
    convneu_app {Γ f g t u na A B} :
      [ Γ |- f ~ g : tProd na A B ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp f t ~ tApp g u : B[t..] ]
  }.

  Class RedTypeProperties :=
  {
    redty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A ⇒* B] -> [Δ |- A⟨ρ⟩ ⇒* B⟨ρ⟩] ;
    redty_sound {Γ A B} : [Γ |- A ⇒* B] -> [Γ |-[de] A ⇒* B] ;
    redty_term {Γ A B} :
      [ Γ |- A ⇒* B : U] -> [Γ |- A ⇒* B ] ;
    redty_refl {Γ A} :
      [ Γ |- A] ->
      [Γ |- A ⇒* A] ;
    redty_trans {Γ} :>
      Transitive (red_ty Γ) ;
  }.

  Class OneStepRedTermProperties :=
  {
    (* osredtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ⇒ u : A] -> [Δ |- t⟨ρ⟩ ⇒ u⟨ρ⟩ : A⟨ρ⟩] ;
    osredtm_sound {Γ A t u} : [Γ |- t ⇒ u : A] -> [Γ |-[de] t ⇒ u : A] ; *)
    osredtm_beta {Γ na A B t u} :
      [ Γ |- A ] ->
      [ Γ ,, vass na A |- t : B ] ->
      [ Γ |- u : A ] ->
      [ Γ |- tApp (tLambda na A t) u ⇒ t[u..] : B[u..] ] ;
    (* osredtm_conv {Γ t u A A'} : 
      [Γ |- t ⇒* u : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- t ⇒* u : A'] ; *)
  }.


  Class RedTermProperties :=
  {
    redtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ⇒* u : A] -> [Δ |- t⟨ρ⟩ ⇒* u⟨ρ⟩ : A⟨ρ⟩] ;
    redtm_sound {Γ A t u} : [Γ |- t ⇒* u : A] -> [Γ |-[de] t ⇒* u : A] ;
    redtm_one_step {Γ A t u} :
      [ Γ |- t ⇒ u : A ] ->
      [ Γ |- t ⇒* u : A ] ;
    redtm_app {Γ na A B f f' t} :
      [ Γ |- f ⇒* f' : tProd na A B ] ->
      [ Γ |- t : A ] ->
      [ Γ |- tApp f t ⇒* tApp f' t : B[t..] ];
    redtm_conv {Γ t u A A'} : 
      [Γ |- t ⇒* u : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- t ⇒* u : A'] ;
    redtm_refl {Γ A t } :
      [ Γ |- t : A] ->
      [Γ |- t ⇒* t : A] ;
    redtm_trans {Γ A} :>
      Transitive (red_tm Γ A) ;
  }.

End GenericTyping.

(** This class bundles together the various predicate and relations, and their
properties all together. Most of the logical relation is constructed over an
abstract instance of this class. *)

Class GenericTypingProperties `(ta : tag)
  `(WfContext ta) `(WfType ta) `(Typing ta)
  `(ConvType ta) `(ConvTerm ta) `(ConvNeuConv ta)
  `(RedType ta) `(OneStepRedTerm ta) `(RedTerm ta) :=
{
  wfc_prop :> WfContextProperties ;
  wfty_prop :> WfTypeProperties ;
  typ_prop :> TypingProperties ;
  convty_prop :> ConvTypeProperties ;
  convtm_prop :> ConvTermProperties ;
  convne_prop :> ConvNeuProperties ;
  redty_prop :> RedTypeProperties ;
  osredtm_prop :> OneStepRedTermProperties ;
  redtm_prop :> RedTermProperties ;
}.

#[export] Hint Resolve wfc_wft wfc_ty wfc_convty wfc_convtm wfc_redty wfc_redtm : gen_typing.
#[export] Hint Resolve wfc_nil wfc_cons wft_wk wft_U wft_prod ty_wk ty_var ty_prod ty_lam ty_app convty_wk convty_uni convty_prod convtm_wk convtm_prod convtm_eta convneu_wk convneu_var convneu_app| 2 : gen_typing.
#[export] Hint Resolve wft_term convty_term convtm_convneu | 4 : gen_typing.
#[export] Hint Resolve ty_conv ty_exp convty_exp convtm_exp convtm_conv convneu_conv redtm_conv | 6 : gen_typing.


Lemma wk_id_ren_on Γ (H : term) : H⟨@wk_id Γ⟩ = H.
Proof. now bsimpl. Qed.

Lemma wk1_ren_on Γ nF F (H : term) : H⟨@wk1 Γ nF F⟩ = H⟨↑⟩.
Proof. now bsimpl. Qed.
  
Lemma wk_up_ren_on Γ Δ (ρ : Γ ≤ Δ) nF F (H : term) : H⟨wk_up nF F ρ⟩ = H⟨upRen_term_term ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_up_wk1_ren_on Γ nF F nG G (H : term) : H⟨wk_up nF F (@wk1 Γ nG G)⟩ = H⟨upRen_term_term ↑⟩.
Proof. now bsimpl. Qed.


Ltac renToWk0 judg :=
  lazymatch judg with
  (** Type judgement, weakening *)
  | [?X ,, vass ?nY ?Y |- ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X nY Y⟩ by apply (wk1_ren_on X nY Y T)
  (** Type judgement, lifting of weakening *)
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨↑⟩ |- _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨_⟩ |- ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up nZ Z (@wk1 X nY Y)⟩ by apply wk_up_wk1_ren_on
  (* Type judgement, lifting *)
  | [?X ,, vass ?nY ?Y⟨wk_to_ren ?r⟩  |- ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up nY Y r⟩ by apply wk_up_wk1_ren_on

  (** Type conversion judgement, weakening *)
  | [?X ,, vass ?nY ?Y |- ?T⟨↑⟩ ≅ _ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X nY Y⟩ by apply (wk1_ren_on X nY Y T)
  | [?X ,, vass ?nY ?Y |- _ ≅ ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X nY Y⟩ by apply (wk1_ren_on X nY Y T)
  (** Type conversion judgement, lifting of weakening *)
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨↑⟩ |- _ ≅ _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨_⟩ |- ?T⟨upRen_term_term ↑⟩ ≅ _ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up nZ Z (@wk1 X nY Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨_⟩ |- _ ≅ ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up nZ Z (@wk1 X nY Y)⟩ by apply wk_up_wk1_ren_on
  (* Type conversion judgement, lifting *)
  | [?X ,, vass ?nY ?Y⟨wk_to_ren ?r⟩  |- ?T⟨upRen_term_term _⟩ ≅ _ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up nY Y r⟩ by apply wk_up_wk1_ren_on
  | [?X ,, vass ?nY ?Y⟨wk_to_ren ?r⟩  |- _ ≅ ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up nY Y r⟩ by apply wk_up_wk1_ren_on

  (** Term judgement, weakening *)
  | [?X ,, vass ?nY ?Y |- _ : ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  | [?X ,, vass ?nY ?Y |- ?t⟨↑⟩ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  (** Term judgement, lifting of weakening *)
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨↑⟩ |- _ : _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨_⟩ |- _ : ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up nZ Z (@wk1 X nY Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨_⟩ |- ?t⟨upRen_term_term ↑⟩ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up nZ Z (@wk1 X nY Y)⟩ by apply wk_up_wk1_ren_on
  (** Term judgement, lifting *)
  | [?X ,, vass ?nY ?Y⟨wk_to_ren ?r⟩ |- _ : ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up nY Y r⟩ by apply wk_up_ren_on
  | [?X ,, vass ?nY ?Y⟨wk_to_ren ?r⟩ |- ?t⟨upRen_term_term _⟩ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up nY Y r⟩ by apply wk_up_ren_on

  (** Term conversion judgement, weakening *)
  | [?X ,, vass ?nY ?Y |- _ ≅ _ : ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  | [?X ,, vass ?nY ?Y |- ?t⟨↑⟩ ≅ _ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  | [?X ,, vass ?nY ?Y |- _ ≅ ?t⟨↑⟩ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  (** Term conversion judgement, lifting of weakening *)
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨↑⟩ |- _ ≅ _ : _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X nY Y⟩ by apply wk1_ren_on
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨_⟩ |- _ ≅ _ : ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up nZ Z (@wk1 X nY Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨_⟩ |- ?t⟨upRen_term_term ↑⟩ ≅ _ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up nZ Z (@wk1 X nY Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, vass ?nY ?Y ,, vass ?nZ ?Z⟨_⟩ |- _ ≅ ?t⟨upRen_term_term ↑⟩ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up nZ Z (@wk1 X nY Y)⟩ by apply wk_up_wk1_ren_on
  (** Term conversion judgement, lifting *)
  | [?X ,, vass ?nY ?Y⟨wk_to_ren ?r⟩ |- _ ≅ _ : ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up nY Y r⟩ by apply wk_up_ren_on
  | [?X ,, vass ?nY ?Y⟨wk_to_ren ?r⟩ |- ?t⟨upRen_term_term _⟩ ≅ _ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up nY Y r⟩ by apply wk_up_ren_on
  | [?X ,, vass ?nY ?Y⟨wk_to_ren ?r⟩ |- _ ≅ ?t⟨upRen_term_term _⟩ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up nY Y r⟩ by apply wk_up_ren_on


  end.

Ltac renToWk :=
  fold ren_term;
  repeat change (ren_term ?x ?y) with y⟨x⟩;
  repeat change S with ↑;
  repeat lazymatch goal with 
  | [ _ : _ |- ?G] => renToWk0 G 
  end.


(** ** Easy consequences of the previous properties. *)

Section GenericConsequences.
  Context `{ta : tag}
  `{!WfContext ta} `{!WfType ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
  `{!RedType ta} `{!OneStepRedTerm ta} `{!RedTerm ta}
  `{!WfContextProperties} `{!WfTypeProperties}
  `{!TypingProperties} `{!ConvTypeProperties}
  `{!ConvTermProperties} `{!ConvNeuProperties}
  `{!RedTypeProperties} `{!OneStepRedTermProperties}
  `{!RedTermProperties}.

  (** *** Properties of well-typed reduction *)

  #[local] Hint Resolve redty_wk redty_term redty_refl redtm_wk redtm_app redtm_refl | 2 : gen_typing.
  #[local] Hint Resolve  redtm_conv | 6 : gen_typing.

  Lemma redty_red {Γ A B} :
      [Γ |- A ⇒* B] -> [ A ⇒* B ].
  Proof.
    intros ?%redty_sound. 
    now eapply redtydecl_red. 
  Qed.

  Lemma redtm_red {Γ t u A} : 
      [Γ |- t ⇒* u : A] ->
      [t ⇒* u].
  Proof.
    intros ?%redtm_sound.
    now eapply redtmdecl_red.
  Qed.

  Lemma redtm_beta {Γ na A B t u} :
      [ Γ |- A ] ->
      [ Γ ,, vass na A |- t : B ] ->
      [ Γ |- u : A ] ->
      [ Γ |- tApp (tLambda na A t) u ⇒* t[u..] : B[u..] ].
  Proof.
    intros; eapply redtm_one_step; 
    now eapply osredtm_beta.
  Qed.

  #[local] Hint Resolve redty_red  redtm_red redtm_beta | 2 : gen_typing.

  Lemma redtywf_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A :⇒*: B] -> [Δ |- A⟨ρ⟩ :⇒*: B⟨ρ⟩].
  Proof.
    intros ? []; constructor; gen_typing.
  Qed.

  Lemma redtywf_sound {Γ A B} : [Γ |- A :⇒*: B] -> TypeRedClosure Γ A B.
  Proof.
    intros []; now eapply redty_sound.
  Qed.

  Lemma redtywf_red {Γ A B} : [Γ |- A :⇒*: B] -> [A ⇒* B].
  Proof.
    intros []; now eapply redty_red.
  Qed.
  
  Lemma redtywf_term {Γ A B} :
      [ Γ |- A :⇒*: B : U] -> [Γ |- A :⇒*: B ].
  Proof.
    intros []; constructor; gen_typing.
  Qed.

  Lemma redtywf_refl {Γ A} : [Γ |- A] -> [Γ |- A :⇒*: A].
  Proof.  constructor; gen_typing.  Qed.

  #[global]
  Instance redtywf_trans {Γ} : Transitive (TypeRedWf Γ). (* fun A B => [Γ |- A :⇒*: B] *)
  Proof.
    intros ??? [] []; unshelve econstructor; try etransitivity; tea.
  Qed.

  (** All properties of type reduction also hold for 
    well-typed type reduction 
    (but we probably don't want to export the instance or the notations will get very puzzling). *)
  Definition redtywf_props : 
    @RedTypeProperties _ _ _ TypeRedWf TermRedWf.
  Proof.
    constructor.
    - intros; now eapply redtywf_wk.
    - intros; now eapply redtywf_sound.
    - intros; now eapply redtywf_term.
    - intros; now apply redtywf_refl.
    - intros; apply redtywf_trans.
  Qed.

  (** Almost all of the RedTermProperties can be derived 
    for the well-formed reduction [Γ |- t :⇒*: u : A]
    but for application (which requires stability of typing under substitution). *)
    
  Definition redtmwf_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t :⇒*: u : A] -> [Δ |- t⟨ρ⟩ :⇒*: u⟨ρ⟩ : A⟨ρ⟩].
  Proof.  intros ? []; constructor; gen_typing. Qed.

  Definition redtmwf_sound {Γ t u A} :
    [Γ |- t :⇒*: u : A] ->  TermRedClosure Γ A t u.
  Proof. intros []; now eapply redtm_sound. Qed.

  Definition redtmwf_red {Γ t u A} :
    [Γ |- t :⇒*: u : A] -> [t ⇒* u].
  Proof. intros []; now eapply redtm_red. Qed.

  Definition redtmwf_conv {Γ} {t u A B} :
      [Γ |- t :⇒*: u : A] ->
      [Γ |- A ≅ B ] ->
      [Γ |- t :⇒*: u : B].
  Proof.
    intros [wfr wfl red] ?.
    constructor.
    all: gen_typing.
  Qed.

  Lemma redtmwf_app {Γ na A B f f' t} :
    [ Γ |- f :⇒*: f' : tProd na A B ] ->
    [ Γ |- t : A ] ->
    [ Γ |- tApp f t :⇒*: tApp f' t : B[t..] ].
  Proof.
    intros [] ?; constructor; gen_typing.
  Qed.

  Lemma wft_simple_arr {Γ A B} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- arr A B].
  Proof.
    intros. eapply wft_prod; renToWk; tea.
    eapply wft_wk; gen_typing.
  Qed.

  Lemma convty_simple_arr {Γ A A' B B'} :
    [Γ |- A] ->
    [Γ |- A ≅ A'] ->
    [Γ |- B ≅ B'] ->
    [Γ |- arr A B ≅ arr A' B'].
  Proof.
    intros; eapply convty_prod; tea.
    1: reflexivity.
    renToWk; eapply convty_wk; gen_typing.
  Qed.

  Lemma ty_simple_app {Γ A B f a} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- f : arr A B] ->
    [Γ |- a : A] ->
    [Γ |- tApp f a : B].
  Proof.
    intros. replace B with B⟨shift⟩[a..] by now asimpl.
    eapply ty_app; tea.
  Qed.

  #[local]
  Hint Resolve ty_simple_app : gen_typing.
  
  Lemma ty_id {Γ A B C} : 
    [Γ |- A] ->
    [Γ |- A ≅ B] ->
    [Γ |- A ≅ C] ->
    [Γ |- idterm A : arr B C].
  Proof.
    intros.
    eapply ty_conv.
    2: eapply convty_simple_arr; cycle 1; tea.
    eapply ty_lam; tea.
    assert (h : [|- Γ ,, vass anDummy A]) by gen_typing.
    eapply (ty_var h (in_here _ _)).
  Qed.

  Lemma convtm_id {Γ A A' B C} : 
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ |- A ≅ A'] ->
    [Γ |- A ≅ B] ->
    [Γ |- A ≅ C] ->
    [Γ |- idterm A ≅ idterm A' : arr B C].
  Proof.
    intros.
    assert [Γ |- A ≅ A] by (etransitivity; tea; now symmetry).
    eapply convtm_conv.
    2: eapply convty_simple_arr; cycle 1; tea.
    eapply convtm_eta; tea.
    2,4: constructor.
    1,2: eapply ty_id; tea; now symmetry.
    assert [|- Γ,, vass anDummy A] by gen_typing.
    assert [Γ,, vass anDummy A |-[ ta ] A⟨@wk1 Γ anDummy A⟩] by now eapply wft_wk. 
    assert [Γ,, vass anDummy A |-[ ta ] A'⟨@wk1 Γ anDummy A⟩] by now eapply wft_wk. 
    eapply convtm_exp.
    - eapply redty_refl; now renToWk.
    - replace A⟨↑⟩ with A⟨↑⟩⟨↑⟩[(tRel 0)..].
      2: asimpl; now rewrite rinstInst'_term.
      eapply redtm_beta; fold ren_term.
      + now renToWk.
      + cbn; refine (ty_var _ (in_here _ _)).
        eapply wfc_cons; tea; now renToWk.
      + now refine (ty_var _ (in_here _ _)).
    - replace A⟨↑⟩ with A⟨↑⟩⟨↑⟩[(tRel 0)..].
      2: asimpl; now rewrite rinstInst'_term.
      eapply redtm_beta; fold ren_term.
      + now renToWk.
      + cbn. eapply (ty_conv (A' := A'⟨↑⟩⟨↑⟩)).
        2:{ 
          renToWk. eapply convty_wk. 
          1: now eapply wfc_cons.
          renToWk. eapply convty_wk; tea.
          now symmetry.
        }
        refine (ty_var _ (in_here _ _)).
        eapply wfc_cons; tea; now renToWk.
      + eapply (ty_conv (A' := A⟨↑⟩)).
        2: renToWk; now eapply convty_wk.
        now refine (ty_var _ (in_here _ _)).
    - cbn. eapply convtm_convneu. eapply convneu_var.
      now refine (ty_var _ (in_here _ _)).
  Qed.
  

  Lemma ty_comp {Γ A B C f g} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- g : arr A B] ->
    [Γ |- f : arr B C] ->
    [Γ |- comp A f g : arr A C].
  Proof.
    intros tyA tyB **. 
    eapply ty_lam; tea.
    assert [|- Γ,, vass anDummy A] by gen_typing.
    pose (r := @wk1 Γ anDummy A).
    eapply ty_simple_app; renToWk.
    - unshelve eapply (wft_wk _ _ tyB) ; tea. 
    - now eapply wft_wk.
    - replace (arr _ _) with (arr B C)⟨r⟩ by (unfold r; now bsimpl).
      now eapply ty_wk.
    - eapply ty_simple_app; renToWk.
      + unshelve eapply (wft_wk _ _ tyA) ; tea. 
      + now eapply wft_wk.
      + replace (arr _ _) with (arr A B)⟨r⟩ by (unfold r; now bsimpl).
        now eapply ty_wk.
      + unfold r; rewrite wk1_ren_on; now refine (ty_var _ (in_here _ _)).
  Qed.


  Lemma redtmwf_refl {Γ a A} : [Γ |- a : A] -> [Γ |- a :⇒*: a : A].
  Proof.
    constructor.
    3: now apply redtm_refl.
    1,2: assumption.
  Qed.

  #[global]
  Instance redtmwf_trans {Γ A} : Transitive (TermRedWf Γ A). (*fun t u => [Γ |- t :⇒*: u : A]*)
  Proof.
    intros ??? [] []; unshelve econstructor; try etransitivity; tea.
  Qed.

  (** *** Lifting properties of untyped reduction to typed reduction. *)

  Lemma redtm_whnf {Γ t u A} : [Γ |- t ⇒* u : A] -> whnf t -> t = u.
  Proof.
    intros.
    apply red_whnf.
    all: gen_typing.
  Qed.

  Lemma redtmwf_whnf {Γ t u A} : [Γ |- t :⇒*: u : A] -> whnf t -> t = u.
  Proof.
    intros []; now eapply redtm_whnf.
  Qed.

  Lemma redtmwf_whne {Γ t u A} : [Γ |- t :⇒*: u : A] -> whne t -> t = u.
  Proof.
    intros ? ?%whnf_whne; now eapply redtmwf_whnf.
  Qed.

  Lemma redty_whnf {Γ A B} : [Γ |- A ⇒* B] -> whnf A -> A = B.
  Proof.
    intros.
    apply red_whnf.
    all: gen_typing.
  Qed.

  Lemma redtywf_whnf {Γ A B} : [Γ |- A :⇒*: B] -> whnf A -> A = B.
  Proof.
    intros []; now eapply redty_whnf.
  Qed.

  Lemma redtywf_whne {Γ A B} : [Γ |- A :⇒*: B] -> whne A -> A = B.
  Proof.
    intros ? ?%whnf_whne; now eapply redtywf_whnf.
  Qed.

  Lemma redtmwf_det Γ t u u' A A' :
    whnf u -> whnf u' ->
    [Γ |- t :⇒*: u : A] -> [Γ |- t :⇒*: u' : A'] ->
    u = u'.
  Proof.
    intros ?? [] [].
    eapply whred_det.
    all: gen_typing.
  Qed.

  Lemma redtywf_det Γ A B B' :
    whnf B -> whnf B' ->
    [Γ |- A :⇒*: B] -> [Γ |- A :⇒*: B'] ->
    B = B'.
  Proof.
    intros ?? [] [].
    eapply whred_det.
    all: gen_typing.
  Qed.

  Lemma whredtm_det Γ t u u' A A' :
    [Γ |- t ↘ u : A] -> [Γ |- t ↘ u' : A'] ->
    u = u'.
  Proof.
    intros [] [].
    eapply whred_det.
    all: gen_typing.
  Qed.

  Lemma whredty_det Γ A B B' :
    [Γ |- A ↘ B] -> [Γ |- A ↘ B'] ->
    B = B'.
  Proof.
    intros [] [].
    eapply whred_det.
    all: gen_typing.
  Qed.

  (** *** Meta-conversion *)
  (** Similar to conversion, but using a meta-level equality rather
  than a conversion *)

  Lemma typing_meta_conv (Γ : context) (t A A' : term) :
    [Γ |- t : A] ->
    A' = A ->
    [Γ |- t : A'].
  Proof.
    now intros ? ->.
  Qed.

  Lemma convtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ≅ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ≅ u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma convne_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ~ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ~ u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ⇒* u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ⇒* u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtmwf_meta_conv_ty (Γ : context) (t u A A' : term) :
    [Γ |- t :⇒*: u : A] ->
    A' = A ->
    [Γ |- t :⇒*: u : A'].
  Proof.
    now intros ? ->. 
  Qed.

  (*** More properties *)

  Lemma well_subst_ext Γ Δ (σ σ' : nat -> term) :
    σ =1 σ' ->
    [Γ |-s σ : Δ] ->
    [Γ |-s σ' : Δ].
  Proof.
    intros Heq.
    induction 1 in σ', Heq |- *.
    all: constructor.
    - eapply IHWellSubst.
      now rewrite Heq.
    - rewrite <- Heq.
      now replace A[↑ >> σ'] with A[↑ >> σ]
        by (now rewrite Heq).
  Qed.

  Lemma redtmwf_appwk {Γ Δ nA A B B' t u a} (ρ : Δ ≤ Γ) :
    [Γ |- t :⇒*: u : tProd nA A B] ->
    [Δ |- a : A⟨ρ⟩] ->
    B' = B⟨upRen_term_term ρ⟩[a..] ->
    [Δ |- tApp t⟨ρ⟩ a :⇒*: tApp u⟨ρ⟩ a : B'].
  Proof.
    intros redtu **.
    eapply redtmwf_meta_conv_ty; tea.
    eapply redtmwf_app; tea.
    unshelve eapply (redtmwf_wk ρ _ redtu).
    gen_typing.
  Qed.

End GenericConsequences.

(** A tactic to transform applications of (untyped) renamings back to (well-typed) weakenings,
so that we can use stability by weakening. *)

#[export] Hint Resolve redtywf_wk redtywf_term redtywf_red redtywf_refl redtmwf_wk redtmwf_app redtmwf_refl redtm_beta redtmwf_red | 2 : gen_typing.
#[export] Hint Resolve  redtmwf_conv | 6 : gen_typing.

  
