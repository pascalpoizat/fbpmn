import React, { Component } from "react";
import { FaFolderOpen, FaDownload, FaPlus } from "react-icons/fa";
import BpmnJS from "bpmn-js/lib/Modeler";
import "bpmn-js/dist/assets/diagram-js.css";
import "bpmn-js/dist/assets/bpmn-font/css/bpmn.css";
import "bpmn-js-properties-panel/dist/assets/bpmn-js-properties-panel.css";
import propertiesPanelModule from "bpmn-js-properties-panel";
import propertiesProviderModule from "bpmn-js-properties-panel/lib/provider/camunda";
import About from "./About.js";
import Verifications from "./Verifications.js";
import VerificationOptions from "./VerificationOptions.js";

const urlVerification = "http://localhost:5000/api/verifications";

export const sleep = async (waitTime) =>
  new Promise((resolve) => setTimeout(resolve, waitTime));

const iconsSize = 22;

/**
 * offer to download a file.
 * @param {String} filename name of the file
 * @param {String} data data contained in the file
 */
function save(filename, data) {
  var blob = new Blob([data], { type: "text/xml" });
  if (window.navigator.msSaveOrOpenBlob) {
    window.navigator.msSaveBlob(blob, filename);
  } else {
    var elem = window.document.createElement("a");
    elem.href = window.URL.createObjectURL(blob);
    elem.download = filename;
    document.body.appendChild(elem);
    elem.click();
    document.body.removeChild(elem);
  }
}

class Modeler extends Component {
  constructor(props) {
    super(props);
    this.state = {
      modeler: "",
      visibility: true,
      launched: false,
      launches: 0,
      networksSelected: [],
      userDefs: null,
      userDefsUsed: null,
      propertiesSelected: [],
      constraintNodeSelected: null,
      constraintEdgeSelected: null,
    };
    this.VerificationsOptions = React.createRef();
  }

  async componentDidMount() {
    this.modeler = new BpmnJS({
      container: "#canvas",
      keyboard: {
        bindTo: window,
      },
      propertiesPanel: {
        parent: "#properties",
      },
      additionalModules: [propertiesPanelModule, propertiesProviderModule],
    });
    try {
      const result = await this.modeler.createDiagram();
      const { warnings } = result;
      console.log(warnings);
    } catch (err) {
      console.log(err.message, err.warnings);
    }
    this.inverseVisibility();
  }

  async exportDiagram() {
    try {
      const result = await this.modeler.saveXML({ format: true });
      const { xml } = result;
      save("diagram.bpmn", xml);
      console.log(xml);
    } catch (err) {
      console.log(err);
    }
  }

  async openDiagram(xml) {
    try {
      const result = await this.modeler.importXML(xml);
      const { warnings } = result;
      console.log(warnings);
    } catch (err) {
      console.log(err.message, err.warnings);
    }
  }

  displayDiagram(DiagramFile) {
    let reader = new FileReader();
    reader.readAsText(DiagramFile);
    reader.onload = (event) => {
      this.openDiagram(event.target.result);
    };
  }

  async sendData() {
    try {
      this.setVerificationOptions();
      const result = await this.modeler.saveXML({ format: true });
      const xml = {
        model: result,
        usernets: this.state.networksSelected,
        userdefs: this.state.userDefs,
        userprops: this.state.propertiesSelected,
        constraintNode: this.state.constraintNodeSelected,
        constraintEdge: this.state.constraintEdgeSelected,
      };
      const xhr = new XMLHttpRequest();
      xhr.open("POST", urlVerification);
      xhr.setRequestHeader("Access-Control-Allow-Headers", "*");
      xhr.setRequestHeader("Access-Control-Allow-Origin", "*");
      xhr.setRequestHeader("Content-Type", "application/json");
      xhr.send(JSON.stringify(xml));
    } catch (err) {
      console.log(err);
    }
  }

  setVerificationOptions() {
    const currentVerificationOptions = this.VerificationsOptions.current;
    const currentNetworksSelected =
      currentVerificationOptions.state.networksChecked;
    const currentUserDefs = currentVerificationOptions.state.defs;
    const currentUserDefsUsed = currentVerificationOptions.state.defsUsed;
    let currentPropertiesSelected =
      currentVerificationOptions.state.propertiesChecked;
    if (currentUserDefsUsed) {
      currentPropertiesSelected =
        currentPropertiesSelected.concat(currentUserDefsUsed);
    }
    const currentConstraintNodeSelected =
      currentVerificationOptions.state.constraintNodeSelected;
    const currentConstraintEdgeSelected =
      currentVerificationOptions.state.constraintEdgeSelected;
    this.setState({
      networksSelected: currentNetworksSelected,
      userDefs: currentUserDefs,
      propertiesSelected: currentPropertiesSelected,
      constraintNodeSelected: currentConstraintNodeSelected,
      constraintEdgeSelected: currentConstraintEdgeSelected,
    });
  }

  async launchVerification() {
    this.sendData();
    this.setState({
      launched: true,
    });
    sleep(500).then(() => {
      fetch(`${urlVerification}/latest`)
        .then((res) => res.json())
        .then((data) => {
          this.setState({
            id: data.id,
            status: data.status,
            launches: this.state.launches + 1,
          });
        });
    });
  }

  updateStatusVerification() {
    if (this.state.launched) {
      fetch(`${urlVerification}/latest`)
        .then((res) => res.json())
        .then((data) => {
          this.setState({
            status: data.status,
            value: data.value,
          });
        });
    }
  }

  inverseVisibility() {
    if (!this.state.visibility) {
      document.getElementById("verifications").style =
        "background-color: #ddd ;   color: black; pointer-events: none ; ";
      document.getElementById("modeler").style = "";
    } else {
      document.getElementById("verifications").style = "";
      document.getElementById("modeler").style =
        "background-color: #ddd ;   color: black; pointer-events: none ; ";
    }
    this.setState({
      visibility: !this.state.visibility,
    });
  }

  render = () => {
    return (
      <div>
        <div id="settings">
          <About></About>
          <span
            id="modeler"
            type="button"
            onClick={() => {
              this.inverseVisibility();
            }}
          >
            Modeler
          </span>
          <VerificationOptions
            ref={this.VerificationsOptions}
          ></VerificationOptions>
          <span
            id="verify"
            onClick={() => {
              this.launchVerification();
            }}
          >
            Verify
          </span>
          <span
            id="verifications"
            type="button"
            onClick={() => {
              this.updateStatusVerification();
              this.inverseVisibility();
            }}
          >
            Verifications
          </span>
        </div>
        <div
          id="modeler"
          style={this.state.visibility ? { display: "none" } : {}}
        >
          <button
            id="open"
            className="button"
            href="true"
            onClick={() => {
              document.getElementById("import-input").click();
            }}
          >
            <FaFolderOpen size={iconsSize} />
          </button>
          <input
            id="import-input"
            onChange={() => {
              this.displayDiagram(
                document.getElementById("import-input").files[0]
              );
            }}
            name="files"
            style={{ display: "none" }}
            type="file"
            accept=".bpmn"
          ></input>
          <button
            id="save"
            className="button"
            href="true"
            onClick={() => {
              this.exportDiagram();
            }}
          >
            <FaDownload size={iconsSize} />
          </button>
          <button
            id="new"
            className="button"
            href="true"
            onClick={() => {
              this.modeler.createDiagram();
            }}
          >
            <FaPlus size={iconsSize} />
          </button>
          <div id="modeler">
            <div
              id="canvas"
              style={{ width: "75%", height: "88vh", float: "left" }}
            ></div>
            <div
              id="properties"
              style={{ width: "25%", float: "right", overflowX: "auto" }}
            ></div>
          </div>
        </div>
        <div
          id="verifications"
          style={this.state.visibility ? {} : { display: "none" }}
        >
          <Verifications
            dataFromParent={this.state.launches}
            statusLastVerif={this.state.status}
            valueLastVerif={this.state.value}
          ></Verifications>
        </div>
      </div>
    );
  };
}

export default Modeler;
