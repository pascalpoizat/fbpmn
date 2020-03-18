# Parameters

#### Entry points
# all, alltla, alljson, allalloy

#### Uncomment the second line to force regeneration, ignoring timestamps.
FORCE = 
#FORCE = force

#### Use fbpmn found in path, or use fbpmn from this repository
#FBPMN = fbpmn
# this yields for instance ../../.stack-work/install/x86_64-linux-tinfo6/51ca166f2298b90eaa8c7df5a7214a4785d26584ed92e1d531dea642040e08c2/8.8.2/bin/fbpmn
FBPMN = $(firstword $(wildcard ../../.stack-work/install/*/*/*/bin/fbpmn))

################

BPMN = $(basename $(notdir $(wildcard src/*.bpmn)))

TLA = $(addprefix tla_from_bpmn/,$(addsuffix .tla,$(BPMN)))
ALLOY = $(addprefix alloy_from_bpmn/,$(addsuffix .als,$(BPMN)))
JSON = $(addprefix json_from_bpmn/,$(addsuffix .json,$(BPMN)))

all : mkdirs alltla alljson allalloy

alltla : mkdirs $(TLA)

allalloy : mkdirs $(ALLOY)

alljson : mkdirs $(JSON)

mkdirs :
	@[ -d tla_from_bpmn ] || mkdir tla_from_bpmn
	@[ -d alloy_from_bpmn ] || mkdir alloy_from_bpmn
	@[ -d json_from_bpmn ] || mkdir json_from_bpmn

tla_from_bpmn/%.tla : src/%.bpmn $(FORCE)
	@echo fbpmn bpmn2tla src/$* tla_from_bpmn/$*
	@$(FBPMN) bpmn2tla src/$* tla_from_bpmn/$*

json_from_bpmn/%.json : src/%.bpmn $(FORCE)
	@echo fbpmn bpmn2json src/$* json_from_bpmn/$*
	@$(FBPMN) bpmn2json src/$* json_from_bpmn/$*

alloy_from_bpmn/%.als : src/%.bpmn $(FORCE)
	@echo fbpmn bpmn2alloy src/$* alloy_from_bpmn/$*
	@$(FBPMN) bpmn2alloy src/$* alloy_from_bpmn/$*

.PHONY : force
force : 
