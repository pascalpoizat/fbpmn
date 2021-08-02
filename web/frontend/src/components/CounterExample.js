import React, { Component } from "react";
import BpmnJS from "bpmn-js/dist/bpmn-viewer.production.min.js";
import "bpmn-js/dist/assets/diagram-js.css";
import "bpmn-js/dist/assets/bpmn-font/css/bpmn.css";
import $ from "jquery";

import "./styles.css";

const urlVerifications = "http://localhost:5000/verifications/";

class CounterExample extends Component {
  constructor(props) {
    super(props);
    this.state = {
      modelContent: "",
      steps: [],
    };
  }

  componentDidMount = () => {
    this.viewer = new BpmnJS({
      container: "#canvas",
    });
    this.token_position = { START: 1, MIDDLE: 2 };
    this.initiateSteps();
    const newUrlModel = `${urlVerifications}${1}/model`;
    fetch(newUrlModel)
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          modelContent: data.content,
        });
        this.openDiagram(this.state.modelContent);
      });
  };

  initiateSteps = () => {
    // elements to highlight
    var nodes;
    var edges;
    var net;

    // step 1
    nodes = new Map([
      ["cStart", 1],
      ["sStart", 1],
    ]);
    edges = new Map([]);
    net = [];

    this.setSteps(nodes, edges, net);

    // step 2
    nodes = new Map([
      ["Client_", 1],
      ["sStart", 1],
    ]);
    edges = new Map([["cE1", 1]]);
    net = [];

    this.setSteps(nodes, edges, net);
    // step 3
    nodes = new Map([
      ["Client_", 1],
      ["cSendCommand", 1],
      ["sStart", 1],
    ]);
    edges = new Map([]);
    net = [];

    this.setSteps(nodes, edges, net);
    // step 4
    nodes = new Map([
      ["Client_", 1],
      ["sStart", 1],
    ]);
    edges = new Map([
      ["cE2", 1],
      ["mf1", 1],
    ]);
    net = new Map([[["Client_", "Supplier_"], ["command"]]]);

    this.setSteps(nodes, edges, net);
    // step 5
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
    ]);
    edges = new Map([
      ["cE2", 1],
      ["sE1", 1],
    ]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 6
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cStoreRequest", 1],
    ]);
    edges = new Map([["sE1", 1]]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 7
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
    ]);
    edges = new Map([
      ["cE3", 1],
      ["sE1", 1],
    ]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 8
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
    ]);
    edges = new Map([
      ["cE3", 1],
      ["sE2", 1],
      ["sE3", 1],
    ]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 9
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["sInvoiceManagement", 1],
    ]);
    edges = new Map([
      ["cE3", 1],
      ["sE2", 1],
    ]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 10
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
    ]);
    edges = new Map([
      ["cE3", 1],
      ["sE2", 1],
      ["sE5", 1],
    ]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 11
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["sPrepareCommand", 1],
    ]);
    edges = new Map([
      ["cE3", 1],
      ["sE5", 1],
    ]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 12
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cReceiveInvoice", 1],
      ["sPrepareCommand", 1],
    ]);
    edges = new Map([["sE5", 1]]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 13
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cReceiveInvoice", 1],
    ]);
    edges = new Map([
      ["sE4", 1],
      ["sE5", 1],
    ]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 14
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cReceiveInvoice", 1],
    ]);
    edges = new Map([["sE6", 1]]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 15
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cReceiveInvoice", 1],
      ["sShipCommand", 1],
    ]);
    edges = new Map([]);
    net = new Map([[["Client_", "Supplier_"], []]]);

    this.setSteps(nodes, edges, net);
    // step 16
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cReceiveInvoice", 1],
    ]);
    edges = new Map([
      ["mf3", 1],
      ["sE7", 1],
    ]);
    net = new Map([
      [["Client_", "Supplier_"], []],
      [["Supplier_", "Client_"], ["goods"]],
    ]);

    this.setSteps(nodes, edges, net);
    // step 17
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cReceiveInvoice", 1],
      ["sSendInvoice", 1],
    ]);
    edges = new Map([["mf3", 1]]);
    net = new Map([
      [["Client_", "Supplier_"], []],
      [["Supplier_", "Client_"], ["goods"]],
    ]);

    this.setSteps(nodes, edges, net);
    // step 18
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cReceiveInvoice", 1],
    ]);
    edges = new Map([
      ["mf2", 1],
      ["mf3", 1],
      ["sE8", 1],
    ]);
    net = new Map([
      [["Client_", "Supplier_"], []],
      [
        ["Supplier_", "Client_"],
        ["goods", "invoice"],
      ],
    ]);

    this.setSteps(nodes, edges, net);
    // step 19
    nodes = new Map([
      ["Client_", 1],
      ["Supplier_", 1],
      ["cReceiveInvoice", 1],
      ["sEnd", 1],
    ]);
    edges = new Map([
      ["mf2", 1],
      ["mf3", 1],
    ]);
    net = new Map([
      [["Client_", "Supplier_"], []],
      [
        ["Supplier_", "Client_"],
        ["goods", "invoice"],
      ],
    ]);
    this.setSteps(nodes, edges, net);
  };

  setSteps = (nodes, edges, net) => {
    this.setState((state) => {
      state.steps.push([nodes, edges, net]);
    });
  };

  markNode(canvas, node) {
    try {
      canvas.addMarker(node, "highlight-node");
    } catch {}
  }

  markEdge(canvas, edge) {
    try {
      canvas.addMarker(edge, "highlight-edge");
    } catch {}
  }

  unmarkNode(canvas, node) {
    try {
      canvas.removeMarker(node, "highlight-node");
    } catch {}
  }

  unmarkEdge(canvas, edge) {
    try {
      canvas.removeMarker(edge, "highlight-edge");
    } catch {}
  }

  showTokensNode(overlays, node, qty) {
    return overlays.add(node, "note", {
      position: { top: -8, right: 8 },
      html: '<div class="diagram-note">' + qty + "</div>",
    });
  }

  valueToJSON(v) {
    return JSON.stringify([...v]);
  }

  edgeBoundingBox(edge) {
    var minx, miny, maxx, maxy;
    if (edge.waypoints) {
      edge.waypoints.forEach((element) => {
        var x = element.x;
        var y = element.y;
        if (x < minx || minx === undefined) {
          minx = x;
        }
        if (y < miny || miny === undefined) {
          miny = y;
        }
        if (x > maxx || maxx === undefined) {
          maxx = x;
        }
        if (y > maxy || maxy === undefined) {
          maxy = y;
        }
      });
    }
    return { minx: minx, miny: miny, maxx: maxx, maxy: maxy };
  }

  positionTokenMiddle(edge) {
    var x, y;
    var rank;
    var bb;
    if (
      edge !== undefined &&
      edge.waypoints !== undefined &&
      edge.waypoints.length >= 2
    ) {
      var wps = edge.waypoints;
      if (wps.length % 2 === 0) {
        // even #wp, take middle of middle segment
        rank = Math.floor((wps.length - 2) / 2);
        var point1 = wps[rank];
        var point2 = wps[rank + 1];
        x = Math.floor((point1.x + point2.x) / 2);
        y = Math.floor((point1.y + point2.y) / 2);
      } else {
        // odd #wp, take middle wp
        rank = Math.floor((wps.length - 1) / 2);
        x = wps[rank].x;
        y = wps[rank].y;
      }
      bb = this.edgeBoundingBox(edge);
      x -= bb.minx;
      y -= bb.miny;
    }
    return { x: x, y: y };
  }

  positionTokenStart(ee) {
    var x, y;
    var bb;
    var wp0;
    if (ee !== undefined) {
      bb = this.edgeBoundingBox(ee);
      wp0 = ee.waypoints[0];
      x = wp0.x - bb.minx;
      y = wp0.y - bb.miny;
    }
    return { x: x, y: y };
  }

  showTokensEdge(registry, overlays, edge, qty, pos) {
    var ee = registry.get(edge);
    switch (pos) {
      case this.token_position.START:
        pos = this.positionTokenStart(ee);
        break;
      case this.token_position.MIDDLE:
      default:
        pos = this.positionTokenMiddle(ee);
    }
    return overlays.add(edge, "note", {
      position: { top: pos.y - 10, left: pos.x - 10 },
      html: '<div class="diagram-note">' + qty + "</div>",
    });
  }

  // should be called with
  // 0 <= prestep <= nbstep-1
  // 0 <= step <= nbstep-1
  animate(
    registry,
    canvas,
    overlays,
    csteps,
    markings,
    prestep,
    step,
    nbsteps,
    pos
  ) {
    // reset markings
    var ns = csteps[prestep][0];
    var es = csteps[prestep][1];
    if (prestep !== step) {
      for (const k of ns.keys()) this.unmarkNode(canvas, k);
      for (const k of es.keys()) this.unmarkEdge(canvas, k);
      for (const id of markings) overlays.remove(id);
    }
    markings = [];
    // do new marking
    ns = csteps[step][0];
    es = csteps[step][1];
    var net = csteps[step][2];

    // set
    for (const k of ns.keys()) {
      this.markNode(canvas, k);
    }
    for (const k of es.keys()) this.markNode(canvas, k);
    for (const [k, v] of ns) {
      try {
        var id = this.showTokensNode(overlays, k, v);
        markings.push(id);
      } catch {}
    }
    for (const [k, v] of es) {
      try {
        id = this.showTokensEdge(registry, overlays, k, v, pos);
        markings.push(id);
      } catch {}
    }
    $("#network #status").html(this.valueToJSON(net));

    return markings;
  }

  async openDiagram(bpmnXML) {
    // import diagram
    try {
      const result = await this.viewer.importXML(bpmnXML);
      const { warnings } = result;
      console.log(warnings);

      // access viewer components
      var canvas = this.viewer.get("canvas");
      var overlays = this.viewer.get("overlays");
      var registry = this.viewer.get("elementRegistry");
      // var moddle = this.viewer.get('moddle');
      // var model = this.viewer.getDefinitions();

      // zoom to fit full viewport
      canvas.zoom("fit-viewport");

      // animation variables
      var markings = [];
      var prestep = 0;
      var step = 0;
      var position = this.token_position.MIDDLE;
      var nbsteps = this.state.steps.length;
      console.log(this.state.steps[0][0]);
      // first drawing
      markings = this.animate(
        registry,
        canvas,
        overlays,
        this.state.steps,
        markings,
        prestep,
        step,
        nbsteps,
        position
      );

      document.body.onkeyup = (e) => {
        if (step < nbsteps - 1 && e.keyCode === 39 && e.shiftKey === false) {
          prestep = step;
          step = step + 1;
          markings = this.animate(
            registry,
            canvas,
            overlays,
            this.state.steps,
            markings,
            prestep,
            step,
            nbsteps,
            position
          );
        } else if (step > 0 && e.keyCode === 37 && e.shiftKey === false) {
          prestep = step;
          step = step - 1;
          markings = this.animate(
            registry,
            canvas,
            overlays,
            this.state.steps,
            markings,
            prestep,
            step,
            nbsteps,
            position
          );
        } else if (e.keyCode === 37 && e.shiftKey === true) {
          prestep = step;
          step = 0;
          markings = this.animate(
            registry,
            canvas,
            overlays,
            this.state.steps,
            markings,
            prestep,
            step,
            nbsteps,
            position
          );
        } else if (e.keyCode === 39 && e.shiftKey === true) {
          prestep = step;
          step = nbsteps - 1;
          markings = this.animate(
            registry,
            canvas,
            overlays,
            this.state.steps,
            markings,
            prestep,
            step,
            nbsteps,
            position
          );
        }
        var title = "&nbsp;step " + (step + 1) + "/" + nbsteps;
        $("#step").html(title);
      };
    } catch (err) {
      console.log(err.message, err.warnings);
    }
  }

  render() {
    return (
      <div>
        <div id="header">
          <div id="title">
            &nbsp;fBPMN Counter Example Animator for
            e002ClientSupplierDynamic.bpmn
          </div>
          <div class="separator">
            <br />
          </div>
          <div id="step">step ../..</div>
        </div>
        <div
          id="canvas"
          style={{
            height: "80vh",
          }}
        ></div>
        <div
          id="network"
          style={{
            width: "99%",
            height: "10vh",
          }}
        >
          <div id="title">Network status</div>
          <div id="status"></div>
        </div>
      </div>
    );
  }
}

export default CounterExample;
