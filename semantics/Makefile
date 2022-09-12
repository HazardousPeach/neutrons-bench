
SOURCES=$(wildcard v1/*.v \
			epics/*.v expr/*.v extract/*.v floatabs/*.v util/*.v validate/*.v) \
		v1/EpicsRecordsBase.v v1/FloatAbsBase.v \
		epics/SpecRecordSetters.v \
		floatabs/RecordSetters.v
FLOCQ=flocq-2.5.1

COQPROJECT := $(shell cat _CoqProject)

.PHONY: all clean

all: Query.hs Query2.hs

Query.hs: v1/Query.vo

Query2.hs: extract/Extract.vo

v1/EpicsRecordsBase.v: v1/EpicsRecordsBase.in gen_record_setters.py
	python3 gen_record_setters.py $< $@ ''

v1/FloatAbsBase.v: v1/FloatAbsBase.in gen_record_setters.py
	python3 gen_record_setters.py $< $@ ''

epics/SpecRecordSetters.v: epics/SpecRecordData.v gen_record_setters.py
	python3 gen_record_setters.py $< $@ 'epics.SpecRecordData'

floatabs/RecordSetters.v: floatabs/RecordData.v gen_record_setters.py
	python3 gen_record_setters.py $< $@ 'floatabs.RecordData'

%.vo: %.v _CoqProject | $(FLOCQ)
	coqc $(COQPROJECT) $<

$(FLOCQ):
	bash setup-flocq.sh

clean:
	$(RM) *.vo *.glob *.v.d */*.vo */*.glob */*.v.d Makefile.coq *.hs coq.d


coq.d: $(SOURCES) _CoqProject | $(FLOCQ)
	coqdep -R . . $(COQPROJECT) $(SOURCES) >$@

include coq.d
