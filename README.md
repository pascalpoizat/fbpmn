# fbpmn

[![Build status](https://secure.travis-ci.org/pascalpoizat/fbpmn.svg)](https://travis-ci.org/pascalpoizat/fbpmn)
[![Windows build status](https://ci.appveyor.com/api/projects/status/github/pascalpoizat/fbpmn?branch=master&svg=true)](https://ci.appveyor.com/project/pascalpoizat/fbpmn)
[![Apache-2.0 license](https://img.shields.io/github/license/pascalpoizat/veca-haskell.svg)](LICENSE)
[![Version](https://img.shields.io/github/tag/pascalpoizat/fbpmn.svg)](fbpmn.cabal)
<!--
<br/>
[![Waffle.io - Columns and their card count](https://badge.waffle.io/pascalpoizat/fbpmn.svg?columns=all)](https://waffle.io/pascalpoizat/fbpmn)
-->
<!--
[![Code Coverage](https://img.shields.io/coveralls/pascalpoizat/fbpmn/master.svg)](https://coveralls.io/github/pascalpoizat/fbpmn)
-->
<!--
<br/>
[![Hackage](https://img.shields.io/hackage/v/fbpmn.svg)](https://hackage.haskell.org/package/fbpmn)
[![Stackage Lts](http://stackage.org/package/fbpmn/badge/lts)](http://stackage.org/lts/package/fbpmn)
[![Stackage Nightly](http://stackage.org/package/fbpmn/badge/nightly)](http://stackage.org/nightly/package/fbpmn)
-->

**formal tools for BPMN**

`fbpmn` supports the verification of business processes (workflows and collaborations) properties:

- option to complete
- proper completion
- no dead activity
- safety
- soundness
- message-relaxed soundness

for six different communication semantics:

- unordered (bag of messages)
- fifo between each couple of processes (array of queues)
- fifo inbox (input queue at each process where messages are added)
- fifo outbox (output queue at each process where messages are fetched)
- global fifo (unique shared queue)
- RSC (realizable with synchronous communication)

**New properties and communication semantics can be easily taken into account** (see Sect. 5).

![Variations.](MBE.png)
*Figure 1: variations and properties (network unordered semantics).*

## 1. Requisites

To verify your BPMN models, you will need:

- 1.1. A Java SE Development Kit (JDK 8), get it [here](https://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html).

	There is an issue (wrt. `tla2tools.jar`) with version 11 so you will need to install version 8. 
- 1.2. The TLA+ tools, get `tla2tools.jar` [here](https://github.com/tlaplus/tlaplus/releases).
	
If you build `fbpmn` from sources (which is required only for **Windows**), you will also need:

- 2.1. The `stack` build system for Haskell, see [here](https://docs.haskellstack.org/en/stable/README/).

	Under **Windows**, due to a bug, please use:
	
	```shell
	curl -sS -ostack.zip -L --insecure https://www.stackage.org/stack/windows-x86_64
	7z x stack.zip stack.exe
	```

## 2. Getting source files

Required for **all platforms** to get the TLA+ theories that are used in the verification process.

You can get the source files in either way:

- 2a. as an archive from [the fbpmn repository](https://github.com/pascalpoizat/fbpmn) by clicking the "Clone or download" button.

- 2b. by cloning the repository using the `git` command.

	```shell
	git clone https://github.com/pascalpoizat/fbpmn
	```

Please then set the `FBPMN_HOME` environment variable to the place where the fbpmn sources have been installed.

```sh
export FBPMN_HOME=/Somewhere/On/Your/Disk/fbpmn
```

You may typically add such a command in your shell configuration file, e.g., `~/.bashrc` or `~/.zshenv` under **Linux** and **OSX**.

## 3a. Getting a pre-built `fbpmn` binary

**Linux** and **OSX** binaries of stable versions of `fbpmn` are built using the continous integration server and are available [here](https://github.com/pascalpoizat/fbpmn/releases).

*We are working on having binaries automatically built for Windows.*

Please then put the `fbpmn` command in a directory that is in your `PATH` environment variable.

## 3b. Building `fbpmn` from source

Required for **Windows**.

```shell
cd fbpmn
stack clean
stack build
stack install
```

This will install the `fbpmn` command in some place that depends on your OS.
You can use `stack path --local-bin` to find out which directory it is.

Please then put this directory in your `PATH` environment variable.

## 4. BPMN models

`fbpmn` is able to deal with **collaborations** either in BPMN or in its own JSON format (see Sect. 7, below). Please note that you can also deal with a standalone **process model** (workflow) as soon as you put it in a standalone pool lane (see some examples of this [here](models/bpmn-origin/src)).

### BPMN format

Please see [the BPMN 2.0 standard](https://www.omg.org/spec/BPMN/2.0/).

The subset of BPMN that we support is presented in Fig. 2.

![BPMN support.](bpmn.png)
*Figure 2: supported subset of the BPMN notation.*

`fbpmn` has been tested with models made with the Camunda Modeler, which you can get [here](https://camunda.com/products/modeler/).

## 5. Verification using TLA+

### Requirements

Verification requires that:

- `FBPMN_HOME` is set to the place where the `fbpmn` sources have been installed (see Sect. 2).
- `TLA2TOOLS_HOME` is set to the place where `tla2tools.jar` is installed (see Sect. 1).
- `fbpmn` is found on the command `PATH` (see Sect. 3a/3b).
- (**optional, available for Linux and OSX only**) `fbpmn-check` and `fbpmn-logs2dot` (from the `scripts` directory of the source distribution) are found on the command `PATH`.<br/> 

### Principles

Verification is achieved in two steps (see Fig. 3):

1. generate a TLA+ representation of the BPMN collaboration
2. use this representation and the TLA+ implementation of our FOL semantics for BPMN collaborations to perform verification (using the `TLC` model checker from the TLA+ tool box).

<img alt="Transformation overview." src="overview.png" width=400><br/>
*Figure 3: `fbpmn` approach to the verification of BPMN collaborations.*

In the sequel, we will use the model in Fig. 4.

![BPMN example.](models/bpmn-origin/png/e037Comm.png)
*Figure 4: example collaboration model (from [https://doi.org/10.1016/j.scico.2018.05.008](https://doi.org/10.1016/j.scico.2018.05.008)).*

**For Linux and OSX users**, we provide you with a `fbpmn-check` script (in the `scripts` directory of the source distribution) that does the two steps described in Fig. 3 for you and performs verification for each possible communication model.

```sh
❯ fbpmn-check $FBPMN_HOME/models/bpmn-origin/src/e037Comm.bpmn
Working in /tmp/e037Comm.PLrCh with 1 worker(s)
transformation done
<<"Processes=", 3, "Nodes=", 29, "Gateway=", 3, "SF=", 23, "MF=", 7>>
---------- Network01Bag ----------
[X] Prop01Type
     states=60 trans=81 depth=32
[X] Prop02Safe
     states=60 trans=81 depth=32
[ ] Prop03Sound
     states=60 trans=81 depth=
[ ] Prop04MsgSound
     states=60 trans=81 depth=
---------- Network02FifoPair ----------
[X] Prop01Type
     states=60 trans=81 depth=32
[X] Prop02Safe
     states=60 trans=81 depth=32
[ ] Prop03Sound
     states=60 trans=81 depth=
[ ] Prop04MsgSound
     states=60 trans=81 depth=
---------- Network04Inbox ----------
[X] Prop01Type
     states=60 trans=81 depth=32
[X] Prop02Safe
     states=60 trans=81 depth=32
[ ] Prop03Sound
     states=60 trans=81 depth=
[ ] Prop04MsgSound
     states=60 trans=81 depth=
---------- Network05Outbox ----------
[X] Prop01Type
     states=60 trans=81 depth=32
[X] Prop02Safe
     states=60 trans=81 depth=32
[ ] Prop03Sound
     states=60 trans=81 depth=
[ ] Prop04MsgSound
     states=60 trans=81 depth=
---------- Network06Fifo ----------
[X] Prop01Type
     states=60 trans=81 depth=32
[X] Prop02Safe
     states=60 trans=81 depth=32
[ ] Prop03Sound
     states=60 trans=81 depth=
[ ] Prop04MsgSound
     states=60 trans=81 depth=
---------- Network07RSC ----------
[X] Prop01Type
     states=60 trans=81 depth=32
[X] Prop02Safe
     states=60 trans=81 depth=32
[ ] Prop03Sound
     states=60 trans=81 depth=
[ ] Prop04MsgSound
     states=60 trans=81 depth=
done.
```

**For Windows users**

*We are working on providing a script for Windows users too.*

Meanwhile, you will have to perform the tasks that are done in `fbpmn-check` by hand.

### Analysing counter-examples

When a model is analysed, counter-examples are generated for each property that does not yield.

**For Linux and OSX users**, using `fbpmn-check`, the counter examples are in `.log` files that are generated in the directory of analysis, e.g., in `/tmp/e037Comm.PLrCh` in the example above.

```sh
❯ ls /tmp/e037Comm.PLrCh/*.log
Network01Bag.Prop01Type.log          Network02FifoPair.Prop01Type.log     Network04Inbox.Prop01Type.log        Network05Outbox.Prop01Type.log       Network06Fifo.Prop01Type.log         Network07RSC.Prop01Type.log
Network01Bag.Prop02Safe.log          Network02FifoPair.Prop02Safe.log     Network04Inbox.Prop02Safe.log        Network05Outbox.Prop02Safe.log       Network06Fifo.Prop02Safe.log         Network07RSC.Prop02Safe.log
Network01Bag.Prop03Sound.log         Network02FifoPair.Prop03Sound.log    Network04Inbox.Prop03Sound.log       Network05Outbox.Prop03Sound.log      Network06Fifo.Prop03Sound.log        Network07RSC.Prop03Sound.log
Network01Bag.Prop04MsgSound.log      Network02FifoPair.Prop04MsgSound.log Network04Inbox.Prop04MsgSound.log    Network05Outbox.Prop04MsgSound.log   Network06Fifo.Prop04MsgSound.log     Network07RSC.Prop04MsgSound.log
``` 

These files include information about the computation time and the counter-examples themselves in a verbose mode, e.g., with all markings given (even if null).

```sh
[...]
State 11: <Action line 177, col 1 to line 177, col 21 of module e037Comm>
/\ edgemarks = [MessageFlow_1j3ru8z |-> 0, MessageFlow_01l3u25 |-> 0, MessageFlow_0jtu5yc |-> 1, MessageFlow_1p97q31 |-> 0, MessageFlow_0y2wjrm |-> 0, MessageFlow_08bo5ej |-> 0, MessageFlow_15n7wk4 |-> 0, SequenceFlow_037u61c |-> 0, SequenceFlow_0dfevt9 |-> 0, Offer_is_not_Interesting |-> 0, Offer_is_Interesting |-> 0, SequenceFlow_1qo309k |-> 0, SequenceFlow_1y19v10 |-> 1, SequenceFlow_1p9f9nn |-> 0, SequenceFlow_0rbkpuc |-> 0, SequenceFlow_1fm8n43 |-> 0, SequenceFlow_1b9yiqz |-> 0, SequenceFlow_10id4f8 |-> 0, SequenceFlow_1wbphor |-> 0, SequenceFlow_1l28um0 |-> 0, SequenceFlow_02xdetn |-> 0, SequenceFlow_06mgtsm |-> 0, SequenceFlow_0wyug2s |-> 0, SequenceFlow_1bhdal8 |-> 1, SequenceFlow_1bxiri7 |-> 0, SequenceFlow_09iuwhk |-> 0, SequenceFlow_1ybfy8r |-> 0, Payment_Was_Made |-> 0, Payment_Was_Not_Made |-> 0, SequenceFlow_1di11xa |-> 0]
/\ net = (<<"Customer_Id", "TravelAgency_Id", "travel">> :> 1)
/\ nodemarks = [Airline_id |-> 0, Ticket_Order_Received |-> 0, Handle_Payment |-> 0, Was_Payment_Made |-> 0, Payment_Confirmed |-> 0, Payment_Refused |-> 0, Confirm_Payment |-> 0, Customer_Id |-> 1, StartEvent_1 |-> 0, Check_Offer |-> 0, Is_the_Offer_Interesting |-> 0, Reject_Offer |-> 0, Book_Travel |-> 0, Offer_Rejected |-> 0, Pay_Travel |-> 0, Booking_Confirmed |-> 0, Payment_Confirmation_Received |-> 0, Travel_Paid |-> 0, TravelAgency_Id |-> 1, Offer_Cancelled |-> 0, Offer_Rejection_Received |-> 0, Status_Waiting |-> 0, Make_Travel_Offer |-> 0, Offer_Needed |-> 0, Ticket_Ordered |-> 0, Order_Ticket |-> 0, IntermediateThrowEvent_0kagqq2 |-> 0, Confirm_Booking |-> 0, Booking_Received |-> 0]
[...]
```

To generate versions of the counter-examples that are **easier to analyse** you can use `fbpmn log2json` (to generate a JSON version of the counter-example) and `fbpmn log2dot` (to generate a graph version of the counter example in the format of the `dot` command). In both cases, the counter-examples are filtered of the markings that are null. You can then use the `dot` command ([see here](https://graphviz.org)) to generate a PNG or a PDF version of the counter example. 

```sh
❯ fbpmn log2dot /tmp/e037Comm.PLrCh/Network01Bag.Prop03Sound /tmp/e037Comm.PLrCh/Network01Bag.Prop03Sound
transformation done
❯ dot -Tpdf -o /tmp/e037Comm.PLrCh/Network01Bag.Prop03Sound.pdf /tmp/e037Comm.PLrCh/Network01Bag.Prop03Sound.dot
❯
```

The first parameter of `fbpmn log2dot` is the source `.log` file and the second one is the target `.dot` file (no sufixes in both cases, `fbpmn` adds them given the type of the read/generated file).

We provide you with a `fbpmn-logs2dot` script (in the `scripts` directory of the source distribution) to generate all `.dot` and `.pdf` files for all `.log` files found in the current directory.

```sh
❯ (cd /tmp/e037Comm.PLrCh; fbpmn-logs2dot)
transformation done
transformation done
transformation done
[...]
```

An excerpt of a counter example for the model in Fig. 4 is given in Fig. 5. For each state (box) there is: the state id, the node markings, the edge markings, and the network status.

[![Counter example image.](Network01Bag.Prop03Sound.excerpt.pdf)](Network01Bag.Prop03Sound.pdf)

*Figure 5: excerpt of the counter example for soundness of the model in Fig. 4 with network unordered semantics (click to see all of it).*

**For Windows users**

When you run TLC to check a model, you can re-direct the output to a `.log` file. Then the `fbpmn log2json` and `fbpmn log2dot` commands presented above can be used.

*We are working on providing a `fbpmn-logs2dot` script for Windows users too.*

### Verification constraints

Some models are unbounded (see *e.g.*, models `e004` to `e006` [here](models/bpmn-origin/src)). To be able to check these models, you may add constraints to the verification process. For this, given your model is in file `myModel.bpmn`, create a file `myModel.constraint` of the form:

```tla
CONSTANT ConstraintNode <- <ConstraintOnNodes>
         ConstraintEdge <- <ConstraintOnEdges>
         Constraint <- <Overall constraint defined in termes of ConstraintNode and ConstraintEdge>
```

The available constraints that you can reuse are defined [here](theories/tla/PWSConstraints.tla) are can be extended.

For example, for model `e006` we may use:

```tla
CONSTANT ConstraintNode <- TRUE
         ConstraintEdge <- MaxEdgeMarking2
         Constraint <- ConstraintNodeEdge
```

that states
that node markings (the maximum number of tokens authorized on a node) is not constrained, 
that edge markings (the maximum number of tokens authorized on an edge) is 2, and
that the overall constraint is to have both the constraint on nodes and the constraint on edges.

### Extending the verification

To add a **new communication model**:

1. define your new communication model semantics, say `MyNet`, in a `NetworkMyNet.tla` file in `$FBPMN_HOME/theories/tla/`
2. copy one of the files in `$FBPMN_HOME/theories/tla/Configs/` to a new file `NetworkNNMyNet.tla` in the same directory, with `NN` being a number different from the existing communication models there
3. in the contents of `NetworkNNMyNet.tla` change the line of the network implementation definition to refer to your new communication model as defined in step 1.

```tla
LOCAL NetworkImpl == INSTANCE NetworkMyNet
```

To add a **new property to verify**:

1. define your new property, say `MyProperty`,  at the end of the `PWSSemantics.tla` file in `$FBPMN_HOME/theories/tla`
2. create a new file `PropNNMyProperty.cfg` in `$FBPMN_HOME/theories/tla/Configs`, with `NN` being a number different from the existing properties there
3. in the contents of `PropNNMyProperty.cfg` refer to your property name as defined in step 1.

```tla
\* run with -deadlock
SPECIFICATION Spec
INVARIANT TypeInvariant

PROPERTY
  MyProperty
```

## 6. Help with `fbpmn`

To get help with `fbpmn`, run `fbpmn -h`.

```sh
❯ fbpmn -h
0.2.6

Usage: fbpmn COMMAND
  formal transformations for BPMN models

Available options:
  -h,--help                Show this help text

Available commands:
  version                  prints the version
  repl                     launches the REPL
  json2dot                 transforms a collaboration from JSON to DOT
  json2tla                 transforms a collaboration from JSON to TLA+
  bpmn2json                transforms a collaboration from BPMN to JSON
  bpmn2tla                 transforms a collaboration from BPMN to TLA+
  log2json                 transforms a TLA+ log from LOG to JSON
  log2dot                  transforms a TLA+ log from LOG to DOT
```

But for the `version`and `repl` commands, you must provide two arguments: the source file and the target file for the transformation.

**No suffixes are to be given for source/target files when running `fbpmn`.**

`fbpmn` also has a REPL mode (run it using `fbpmn repl`) including the following commands:

```
quit (quit REPL)
help (list commands)
load (load current graph from JSON and verify file)
bpmn (load current graph from BPMN)
json (save current graph to JSON)
dot  (save current graph to DOT)
tla  (save current graph to TLA+)
```

**Suffixes are to be given when using the REPL.**

## 7. JSON format

The JSON format for a model can be generated from the BPMN format of it, using `fbpmn bpmn2json`.
In general, there should therefore be no need to write out models in the JSON format manually.

Examples of models are given [here](models/bpmn-origin/json_from_bpmn) for files generated from BPMN, and [here](models/json-origin) for files created manually.

To help in writing the JSON format, `fbpmn` has a very basic output to the format of the `dot` command ([graphviz format](https://graphviz.org)).
To transform a JSON file into DOT, run:

```shell
fbpmn json2dot sourcefile targetfile
```

where neither `sourcefile` nor `targetfile` have a suffix (the correct ones will be added by `fbpmn`).
Then provided you have `dot` installed, you can generate a PNG picture for your collaboration, using:

```shell
dot -Tpng sourcefile.dot -o targetfile.png
```

