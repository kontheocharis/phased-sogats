module Translation.PSOGAT-to-SOGAT where

open import Theories.Phase
import Theories.SO.SOGAT as SO
import Theories.FO.CwF as FO-CwF
import Theories.FO.GAT as FO-GAT
import Theories.FO.SOGAT as FO-SOGAT
import Theories.FO.PSOGAT as FO

module PSOGAT-to-SOGAT (Φ : PhaseAlg) (sogat : SO.SOGAT-ToS) where
  -- In here, we pretend to be in a two-level type theory where the
  -- object theory is the SOGAT ToS, given by the `sogat` module parameter.
  open SO.SOGAT-ToS sogat

  -- What we will do is build a model of PSOGAT ToS in Psh(Φ, Ty), that is,
  -- presheaves over the input phase algebra, valued in the object universe.

  module P = FO.PSOGAT-ToS
  module S = FO-SOGAT.SOGAT-ToS
  module G = FO-GAT.GAT-ToS
  module C = FO-CwF.CwF
  module Cˢ = FO-CwF.CwFSorts
  module Cᶜ = FO-CwF.InCwFSorts.CwFCtors
  module Gᶜ = FO-GAT.InCwF.GATCtors
  module Sᶜ = FO-SOGAT.InGAT.SOGATCtors
  module Pᶜ = FO.InSOGAT.PSOGATCtors

  fo-psogat : FO.PSOGAT-ToS Φ
  fo-psogat .P.sogat .S.gat .G.cwf .C.sorts .Cˢ.Con = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.sorts .Cˢ.Sub = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.sorts .Cˢ.Ty = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.sorts .Cˢ.Tm = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.id = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ._∘_ = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.id∘ = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.∘id = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.assoc = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.∙ = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.ε = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.∃!ε = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ._[_]T = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.[id]T = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.[∘]T = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ._[_] = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.[id] = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.[∘] = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ._▷_ = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.p = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.q = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ._,_ = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.p∘, = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.,∘ = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.p,q = {!!}
  fo-psogat .P.sogat .S.gat .G.cwf .C.ctors .Cᶜ.q[,] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.`1 = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.`1[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.unit-uniq = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.top[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Σ = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Σ[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.pair-proj = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.U = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.U[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.El = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.El[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Π = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Π[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.lam-app = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.lam[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Eq = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Eq[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.refl-reflect = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Refl[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Πᴱ = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.Πᴱ[] = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.lam-appᴱ = {!!}
  fo-psogat .P.sogat .S.gat .G.gat-ctors .Gᶜ.lamᴱ[] = {!!}
  fo-psogat .P.sogat .S.sogat-ctors .Sᶜ.Uᴿ = {!!}
  fo-psogat .P.sogat .S.sogat-ctors .Sᶜ.Uᴿ[] = {!!}
  fo-psogat .P.sogat .S.sogat-ctors .Sᶜ.elᴿ = {!!}
  fo-psogat .P.sogat .S.sogat-ctors .Sᶜ.elᴿ[] = {!!}
  fo-psogat .P.sogat .S.sogat-ctors .Sᶜ.Πᴿ = {!!}
  fo-psogat .P.sogat .S.sogat-ctors .Sᶜ.lam-appᴿ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.In = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.In[] = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.In-prop = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.in⊤ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.in-and-proj = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.Πᴾ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.↑↓ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.Πᴾᴿ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.↑↓ᴿ = {!!}
