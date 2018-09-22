COQFLAGS=-coqlib "$(COQLIB)"
COQDOCFLAGS=-coqlib_path "$(COQLIB)" --latex -g
COQC="$(COQBIN)"/coqc $(COQFLAGS)
COQDOC="$(COQBIN)"/coqdoc $(COQDOCFLAGS)


.SUFFIXES: .v .vo .tex

.v.vo:
	$(COQC) $*
.v.tex:
	$(COQDOC) $*.v


typedlambda.tex: typedlambda.v
typedopsem.tex: typedopsem.v
typeddensem.tex: typeddensem.v
typedsubst.tex: typedsubst.v
typedsoundness.tex: typedsoundness.v
typedadequacy.tex: typedadequacy.v

utility.vo: utility.v
Sets.vo: Sets.v

PredomCore.vo: PredomCore.v
PredomProd.vo: PredomProd.v PredomCore.vo
PredomSum.vo: PredomSum.v PredomCore.vo
PredomLift.vo: PredomLift.v PredomCore.vo utility.vo
PredomKleisli.vo: PredomKleisli.v PredomLift.vo PredomProd.vo PredomCore.vo utility.vo
PredomFix.vo: PredomFix.v PredomCore.vo PredomProd.vo PredomLift.vo PredomKleisli.vo
KnasterTarski.vo: KnasterTarski.v Sets.vo PredomCore.vo PredomProd.vo
lc.vo: lc.v PredomCore.vo PredomProd.vo PredomSum.vo PredomLift.vo PredomFix.vo PredomKleisli.vo
PredomAll.vo: PredomAll.v PredomCore.vo PredomProd.vo PredomSum.vo PredomLift.vo PredomKleisli.vo PredomFix.vo 

uni.vo: uni.v utility.vo 
unisem.vo: unisem.v PredomAll.vo lc.vo uni.vo
uniade.vo: uniade.v unisem.vo  KnasterTarski.vo Sets.vo PredomAll.vo
unisound.vo: unisound.v unisem.vo PredomAll.vo

typedlambda.vo: typedlambda.v utility.vo
typedopsem.vo: typedopsem.v typedlambda.vo
typeddensem.vo: typeddensem.v PredomAll.vo typedlambda.vo
typedsubst.vo: typedsubst.v typeddensem.vo
typedsoundness.vo: typedsoundness.v typedsubst.vo typedopsem.vo
typedadequacy.vo: typedadequacy.v typeddensem.vo typedopsem.vo

all: typedadequacy.vo typedsoundness.vo unisound.vo uniade.vo



