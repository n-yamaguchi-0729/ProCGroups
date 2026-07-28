import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorQuotientMutualMapData
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorMap
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Core
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorReplacement
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorAddition
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorDeletion
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Script

/-!
# Tietze equivalences and verified scripts

This aggregate separates semantic presentation equivalence from syntactic
transformations.  The core and generator/relator operation modules construct
certificates; `Tietze.Script` records well-typed elementary move sequences and
their trace and cost.
-/
