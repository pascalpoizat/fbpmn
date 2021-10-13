# fbpmn

[![Build status](https://travis-ci.com/pascalpoizat/fbpmn.svg?branch=master)](https://travis-ci.com/github/pascalpoizat/fbpmn)
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

---

**NEW: fBPMN Web Application (since v0.3.8)**

We provide the user with a Web application of `fbpmn` so that its installation and use is made easier.

To use it:

- install [Docker](https://www.docker.com) on your computer
- clone `fbpmn` from the GitHub repository [here](https://github.com/pascalpoizat/fbpmn)
- go to `fbpmn/web`
- read `README.md`
- run `docker-compose build` and then `docker-compose up`
- open [http://localhost:3000/](http://localhost:3000/)

Note: sBPMN (see below) is not yet supported in the Web application.

Note: the old fBPMN Web application, available [here](http://vacs.enseeiht.fr/bpmn/) is now deprecated. It may stop operating at any time.

---

**NEW: sBPMN, BPMN extension for spatial information (since v0.3.6)**

To use it:

- install `fbpmn` as explained below
- in addition to steps _1. -- 5._ below, ensure `sfbpmn-check` from the `scripts/` directory is found on your command `PATH`
- design your model (`M.bpmn`), user definitions (`M.userdefs`, optional), user specific properties (`M.userprops`, optional), and boundedness constraints (`M.constraint`, optional); see models with ids `s0xx` in the `models/bpmn-origin/src` for examples
- verify your model with `sfbpmn-check M.bpmn cores` (the script will check if the optional files are there or not, `cores` is the number of cores to uses)

---

**In next releases**

- more documentation on associating time information to time-related BPMN constructs (available since v0.3.4)
- more documentation on sBPMN extension fields (available since v0.3.6)
- alignment between the `fbpmn-check` and `sfbpmn-check` verification scripts
- support for sBPMN in the Web application
- pre-built Docker image

---

`fbpmn` supports the verification of business processes (workflows and collaborations) properties:

- option to complete
- proper completion
- no dead activity
- safety
- soundness
- message-relaxed soundness

for seven different communication semantics:

- **Bag** (shared message multiset, no ordering)
- **Fifo all** (shared message queue, ordering _wrt._ emission time)
- **Causal**, (shared message causality structure, ordering _wrt._ message emission causality)
- **Realizable with Synchronous Communication (RSC)** (shared 1-sized message buffer)
- **Fifo pair** (message queue for each couple of processes, ordering _wrt._ emission time)
- **Fifo inbox** (input message queue for each process, ordering _wrt._ emission time)
- **Fifo outbox**, (output message queue for each process, ordering _wrt._ emission time)

**New properties and communication semantics can be easily taken into account** (see Sect. 5, _Extending the verification_).

### References

- Rim Saddem-Yagoubi, Pascal Poizat, and Sara Houhou. **Business Processes Meet Spatial Concerns: the sBPMN Verification Framework.** In: _24th International Symposium on Formal Methods (FM)_, 2021.

- Sara Houhou, Souheib Baarir, Pascal Poizat, and Philippe Quéinnec. **A Direct Formal Semantics for BPMN Time-Related Constructs.** In: _16th International Conference on Evaluation of Novel Approaches to Software Engineering (ENASE)_, 2021.

- Sara Houhou, Souheib Baarir, Pascal Poizat, Philippe Quéinnec, and Laïd Kahloul. **A First-Order Logic Verification Framework for Communication-Parametric and Time-Aware BPMN Collaborations**. _Information Systems_, 2021.

- Sara Houhou, Souheib Baarir, Pascal Poizat, and Philippe Quéinnec. **A First-Order Logic Semantics for Communication-Parametric BPMN Collaborations**. In: _17th International Conference on Business Process Management (BPM)_, Springer, 2019.

### TL;DR for the impatient

Since we now provide you with a new Web application, all this can also be performed using it. If you like it the "command line interface" way, here is the procedure:

1. use the modeler of your choice to model a process or a collaboration
   ![BPMN example.](e033MBE.png)
2. verify your model for all combinations of property and communication semantics

   ```sh
   ❯ fbpmn-check $FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
   Working in /tmp/e033MBE.T07y4 with 2 worker(s)
   transformation done
   <<"Processes=", 2, "Nodes=", 22, "Gateway=", 4, "SF=", 20, "MF=", 6>>
   ---------- Network01Bag ----------
   [X] Prop01Type
        states=101 trans=169 depth=23
   [X] Prop02Safe
        states=101 trans=169 depth=23
   [ ] Prop03Sound
        states=101 trans=169 depth=
   [X] Prop04MsgSound
        states=101 trans=169 depth=23
   [... other communication semantics ...]
   done.
   ```

3. generate interactive counter example exploration pages for all `fbpmn-check` analysis log files

   ```sh
   ❯ (cd /tmp/e033MBE.T07y4; fbpmn-log-transform html)
   transformation done
   transformation done
   transformation done
   [...]
   ```

4. open one of the generated files with a browser and play with the counter example using &leftarrow;/&rightarrow;/`Shift`&leftarrow;/`Shift`&rightarrow; on your keyboard

   ![step 24](animation_24.png)

   |              01              |          ...          |              12              |              13              |              14              |          ...          |              24              |
   | :--------------------------: | :-------------------: | :--------------------------: | :--------------------------: | :--------------------------: | :-------------------: | :--------------------------: |
   | ![step 01](animation_01.png) | ![](animation_00.png) | ![step 12](animation_12.png) | ![step 13](animation_13.png) | ![step 14](animation_14.png) | ![](animation_00.png) | ![step 24](animation_24.png) |

   **note:** for security issues, and since the interactive counter example exploration pages load local files (your BPMN models), you will have either to:

   - (preferred) serve the pages using a server such as [http-server](https://www.npmjs.com/package/http-server) or [SimpleHTTPServer](https://docs.python.org/2/library/simplehttpserver.html).

     ```sh
     ❯ npm install -g http-server # run only once to install http-server
     ❯ (cd /tmp/e033MBE.T07y4; http-server .)
     ```

     ```sh
     ❯ (cd /tmp/e033MBE.T07y4; python2 -m SimpleHTTPServer 8080) # for Python 2
     ❯ (cd /tmp/e033MBE.T07y4; python3 -m http.server 8080) # for Python 3
     ```

   - (not recommended) de-activate local file restrictions, see [here](https://github.com/mrdoob/three.js/wiki/How-to-run-things-locally).

## 1. Requisites

To verify your BPMN models, you will need:

- 1.1. A Java SE Development Kit, get it [here](https://www.oracle.com/technetwork/java/javase/downloads/index.html).

- 1.2. The TLA+ tools, get `tla2tools.jar` [here](https://github.com/tlaplus/tlaplus/releases).

- 1.3. The task-based command-line shell and scripting language Powershell, get it [here](https://docs.microsoft.com/en-us/powershell/scripting/install/installing-powershell?view=powershell-7.1)

:warning: `fbpmn` is known to be working with:

- Java 12 and TLA+ tools version 1.6.0 (not 1.5.7)
- Java 8 and TLA+ tools version 1.5.7 or 1.6.0

If you build `fbpmn` from sources (not required in most situations since binaries are available, see Sect. 3a), you will also need:

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

You may typically add such a command in your shell configuration file, e.g., `~/.bashrc` or `~/.zshenv` under **Linux** and **MacOS**.

## 3a. Getting a pre-built `fbpmn` binary

**Linux**, **MacOS**, and **Windows** binaries of stable versions of `fbpmn` are built using the continuous integration server and are available [here](https://github.com/pascalpoizat/fbpmn/releases).

Please then put the `fbpmn` command in a directory that is in your `PATH` environment variable.

## 3b. Building `fbpmn` from source

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

`fbpmn` is able to deal with **collaborations** either in BPMN or in its own JSON format (see Sect. 7, below). Please note that you can also deal with a standalone **process model** (workflow) as long as you put it in a standalone pool lane (see some examples of this [here](models/bpmn-origin/src)).

### BPMN format

Please see [the BPMN 2.0 standard](https://www.omg.org/spec/BPMN/2.0/).

The subset of BPMN that we support is presented in Fig. 1.

![BPMN support.](bpmn.png)
_Figure 1: supported subset of the BPMN notation._

`fbpmn` has been tested with models made with the Camunda Modeler, which you can get [here](https://camunda.com/products/modeler/).

## 5. Verification using TLA+

### Requirements

Verification requires that:

- `FBPMN_HOME` is set to the place where the `fbpmn` sources have been installed (see Sect. 2).
- `TLA2TOOLS_HOME` is set to the place where `tla2tools.jar` is installed (see Sect. 1).
- `fbpmn` is found on the command `PATH` (see Sect. 3a/3b).
- `fbpmn-check` and `fbpmn-log-transform` (from the `scripts` directory of the source distribution) are found on the command `PATH`.

### Principles

Verification is achieved in two steps (see Fig. 2):

1. generate a TLA+ representation of the BPMN collaboration
2. use this representation and the TLA+ implementation of our FOL semantics for BPMN collaborations to perform verification (using the `TLC` model checker from the TLA+ tool box).

<img alt="Transformation overview." src="overview.png" width=400><br/>
_Figure 2: `fbpmn` approach to the verification of BPMN collaborations._

In the sequel, we will use the model in Fig. 3.

![BPMN example.](e033MBE.png)
_Figure 3: example collaboration model (`e033MBE.bpmn`)._

We provide you with a `fbpmn-check` script (in the `scripts` directory of the source distribution) that does the two steps described in Fig. 2 for you and performs verification for each possible communication model.

```sh
❯ fbpmn-check $FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
Working in /tmp/e033MBE.T07y4 with 2 worker(s)
transformation done
<<"Processes=", 2, "Nodes=", 22, "Gateway=", 4, "SF=", 20, "MF=", 6>>
---------- Network01Bag ----------
[X] Prop01Type
     states=101 trans=169 depth=23
[X] Prop02Safe
     states=101 trans=169 depth=23
[ ] Prop03Sound
     states=101 trans=169 depth=
[X] Prop04MsgSound
     states=101 trans=169 depth=23
---------- Network02FifoPair ----------
[X] Prop01Type
     states=101 trans=169 depth=23
[X] Prop02Safe
     states=101 trans=169 depth=23
[ ] Prop03Sound
     states=101 trans=169 depth=
[X] Prop04MsgSound
     states=101 trans=169 depth=23
---------- Network03Causal ----------
[X] Prop01Type
     states=105 trans=173 depth=23
[X] Prop02Safe
     states=105 trans=173 depth=23
[ ] Prop03Sound
     states=105 trans=173 depth=
[X] Prop04MsgSound
     states=105 trans=173 depth=23
---------- Network04Inbox ----------
[X] Prop01Type
     states=101 trans=169 depth=23
[X] Prop02Safe
     states=101 trans=169 depth=23
[ ] Prop03Sound
     states=101 trans=169 depth=
[X] Prop04MsgSound
     states=101 trans=169 depth=23
---------- Network05Outbox ----------
[X] Prop01Type
     states=101 trans=169 depth=23
[X] Prop02Safe
     states=101 trans=169 depth=23
[ ] Prop03Sound
     states=101 trans=169 depth=
[X] Prop04MsgSound
     states=101 trans=169 depth=23
---------- Network06Fifo ----------
[X] Prop01Type
     states=120 trans=194 depth=23
[X] Prop02Safe
     states=120 trans=194 depth=23
[ ] Prop03Sound
     states=120 trans=194 depth=
[ ] Prop04MsgSound
     states=120 trans=194 depth=
---------- Network07RSC ----------
[X] Prop01Type
     states=60 trans=92 depth=20
[X] Prop02Safe
     states=60 trans=92 depth=20
[ ] Prop03Sound
     states=60 trans=92 depth=
[ ] Prop04MsgSound
     states=60 trans=92 depth=
done.

```

Verification for a single communication model and choosing the properties of interest is also possible but requires some more commands to run (mostly copying files and launching Java, as can be seen in `fbpmn-check`). _We are working on an extension of `fbpm-check` with options to help there._

### Analysing counter-examples

When a model is analysed, counter-examples are generated for each property that does not yield.

Using `fbpmn-check`, the counter examples are in `.log` files that are generated in the directory of analysis, e.g., in `/tmp/e033MBE.T07y4` in the example above.

```sh
❯ (cd /tmp/e033MBE.T07y4; ls *.log)
e033MBE.Network01Bag.Prop01Type.log          e033MBE.Network03Causal.Prop03Sound.log      e033MBE.Network06Fifo.Prop01Type.log
e033MBE.Network01Bag.Prop02Safe.log          e033MBE.Network03Causal.Prop04MsgSound.log   e033MBE.Network06Fifo.Prop02Safe.log
e033MBE.Network01Bag.Prop03Sound.log         e033MBE.Network04Inbox.Prop01Type.log        e033MBE.Network06Fifo.Prop03Sound.log
e033MBE.Network01Bag.Prop04MsgSound.log      e033MBE.Network04Inbox.Prop02Safe.log        e033MBE.Network06Fifo.Prop04MsgSound.log
e033MBE.Network02FifoPair.Prop01Type.log     e033MBE.Network04Inbox.Prop03Sound.log       e033MBE.Network07RSC.Prop01Type.log
e033MBE.Network02FifoPair.Prop02Safe.log     e033MBE.Network04Inbox.Prop04MsgSound.log    e033MBE.Network07RSC.Prop02Safe.log
e033MBE.Network02FifoPair.Prop03Sound.log    e033MBE.Network05Outbox.Prop01Type.log       e033MBE.Network07RSC.Prop03Sound.log
e033MBE.Network02FifoPair.Prop04MsgSound.log e033MBE.Network05Outbox.Prop02Safe.log       e033MBE.Network07RSC.Prop04MsgSound.log
e033MBE.Network03Causal.Prop01Type.log       e033MBE.Network05Outbox.Prop03Sound.log
e033MBE.Network03Causal.Prop02Safe.log       e033MBE.Network05Outbox.Prop04MsgSound.log
```

These files include information about the computation time and the counter-examples themselves in a verbose mode.

```sh
[...]
State 13: <Action line 156, col 1 to line 156, col 21 of module e033MBE>
/\ edgemarks = [MessageFlow_0qo10kt |-> 0, MessageFlow_1a8bsa8 |-> 0, MessageFlow_1r7fyxg |-> 0, MessageFlow_091cszi |-> 0, MessageFlow_1tq79cn |-> 1, MessageFlow_1okf1vd |-> 0, SequenceFlow_0nps006 |-> 0, SequenceFlow_1wtnl4z |-> 0, SequenceFlow_0o5vg8x |-> 0, SequenceFlow_0fplzau |-> 1, SequenceFlow_1dte0vc |-> 0, SequenceFlow_0k086s0 |-> 0, SequenceFlow_0698suh |-> 0, SequenceFlow_1wgoun9 |-> 0, SequenceFlow_16ovyt7 |-> 0, SequenceFlow_0mgjt9y |-> 0, SequenceFlow_1xvdo11 |-> 1, SequenceFlow_1y1oo45 |-> 0, SequenceFlow_0rjtib7 |-> 0, SequenceFlow_0k02j79 |-> 0, SequenceFlow_0f0ojke |-> 0, SequenceFlow_1oxapbj |-> 0, SequenceFlow_096ubuj |-> 0, SequenceFlow_0eej3d6 |-> 0, SequenceFlow_0jq12xx |-> 0, SequenceFlow_0v4m6o8 |-> 0]
/\ net = (<<"P_id", "Q_id", "results">> :> 1)
/\ nodemarks = [P_id |-> 1, StartEvent_1 |-> 0, Task_05seu1l |-> 0, Task_0yk02ke |-> 0, BoundaryEvent_1fgc3dg |-> 0, EndEvent_1yasgxk |-> 0, ExclusiveGateway_06st2fh |-> 0, IntermediateThrowEvent_16df5b4 |-> 0, Task_1lnz72e |-> 0, Task_1ypg0u2 |-> 0, Q_id |-> 1, StartEvent_1axpofs |-> 0, Task_0k7ip70 |-> 0, IntermediateThrowEvent_0yo36nb |-> 0, ExclusiveGateway_0phbzc0 |-> 0, IntermediateThrowEvent_1ewiw3i |-> 0, ExclusiveGateway_14e5fg8 |-> 0, IntermediateThrowEvent_0nfi6to |-> 0, EndEvent_0l9fmhf |-> 0, ExclusiveGateway_06aycf0 |-> 0, IntermediateThrowEvent_1s2ehzf |-> 0, IntermediateThrowEvent_1q2mw0e |-> 0]
[...]
```

To generate versions of the counter-examples that are **easier to analyse** you can use:

- `fbpmn log2json` to get a JSON version of the counter-example

  ```sh
  ❯ fbpmn log2json /tmp/e033MBE.T07y4/e033MBE.Network01Bag.Prop03Sound /tmp/e033MBE.T07y4/e033MBE.Network01Bag.Prop03Sound
  transformation done
  ```

- `fbpmn log2dot` to get a graph version of the counter example in the format of the `dot` command ([see here](https://graphviz.org)) and then use this command to generate PDF or PNG images.

  ```sh
  ❯ fbpmn log2dot /tmp/e033MBE.T07y4/e033MBE.Network01Bag.Prop03Sound /tmp/e033MBE.T07y4/e033MBE.Network01Bag.Prop03Sound
  transformation done
  ```

- `fbpmn log2html` to generate an interactive counter example exploration page (use the &leftarrow;/&rightarrow; keys to navigate between states of the counter example, in combination with the `Shift`key to go the the start/end of the counter example).

  ```sh
  ❯ fbpmn log2html /tmp/e033MBE.T07y4/e033MBE.Network01Bag.Prop03Sound /tmp/e033MBE.T07y4/e033MBE.Network01Bag.Prop03Sound
  transformation done
  ```

  An excerpt of a counter example for the model in Fig. 3 is given in Fig. 4.

  [![Counter example animation (step 24).](animation_24.png)](e033MBE.Network01Bag.Prop03Sound.html)

  _Figure 4: last state of the animation of the counter example for soundness of the model in Fig. 4 with network unordered semantics._

The first parameter of the three commands is the source `.log` file and the second one is the target `.json`/`.dot`/`.html` file (no suffixes in both cases, `fbpmn` adds them given the type of the read/generated file).

In all three cases, the counter-examples are filtered of the markings that are null.

To perform these transformations **for all `.log` files contained in the current directory**,
we provide you with a `fbpmn-log-transform` script (in the `scripts` directory of the source distribution) for which you can precise the kind of files to generate (`json`/`dot`/`html`).

```sh
❯ (cd /tmp/e033MBE.T07y4; fbpmn-log-transform html)
transformation done
transformation done
transformation done
[...]
```

### Verification constraints

Some models are unbounded (see _e.g._, models `e004` to `e006` [here](models/bpmn-origin/src)). To be able to check these models, you may add constraints to the verification process. For this, given your model is in file `myModel.bpmn`, create a file `myModel.constraint` of the form:

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

1. define your new property, say `MyProperty`, at the end of the `PWSSemantics.tla` file in `$FBPMN_HOME/theories/tla`
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
➜ fbpmn -h
0.3.8

Usage: fbpmn COMMAND
  formal transformations for BPMN models

Available options:
  -h,--help                Show this help text

Available commands:
  version                  prints the version
  json2dot                 transforms a model from JSON to DOT
  json2tla                 transforms a model from JSON to TLA+
  json2alloy               transforms a model from JSON to Alloy
  bpmn2json                transforms a model from BPMN to JSON
  bpmn2tla                 transforms a model from BPMN to TLA+
  bpmn2alloy               transforms a model from BPMN to Alloy
  sbpmn2tla                transforms a model from space BPMN to TLA+
  log2json                 transforms a TLA+ log from LOG to JSON
  log2dot                  transforms a TLA+ log from LOG to DOT
  log2html                 transforms a TLA+ log from LOG to HTML
  slog2html                transforms a TLA+ space log from LOG to HTML
```

But for the `version` command, you must provide two arguments: the source file and the target file for the transformation.

**No suffixes are to be given for source/target files when running `fbpmn`.**

## 7. JSON format

The JSON format for a model can be generated from the BPMN format of it, using `fbpmn bpmn2json`.
In general, there should therefore be no need to write out models in the JSON format manually.

Examples of models are given [here](models/bpmn-origin/json_from_bpmn) for files generated from BPMN.

To help in writing the JSON format, `fbpmn` has a very basic output to the format of the `dot` command ([see here](https://graphviz.org)).
To transform a JSON file into DOT, run:

```shell
fbpmn json2dot sourcefile targetfile
```

where neither `sourcefile` nor `targetfile` have a suffix (the correct ones will be added by `fbpmn`).
Then provided you have `dot` installed, you can generate a PNG picture for your collaboration, using:

```shell
dot -Tpng sourcefile.dot -o targetfile.png
```
