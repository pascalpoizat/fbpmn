import React, { Component } from 'react';
import { FaFolderOpen, FaDownload, FaPlus } from 'react-icons/fa';
import BpmnJS from 'bpmn-js/lib/Modeler';
import 'bpmn-js/dist/assets/diagram-js.css';
import 'bpmn-js/dist/assets/bpmn-font/css/bpmn.css';
import propertiesPanelModule from 'bpmn-js-properties-panel';
import propertiesProviderModule from 'bpmn-js-properties-panel/lib/provider/bpmn';
import About from "./../About.js";
import Verifications from "../Verifications.js";

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

export const sleep = async (waitTime) =>
    new Promise(resolve =>
        setTimeout(resolve, waitTime));


const iconsSize = 22;
class BpmnModelerComponent extends Component {
    constructor(props) {
        super(props);
        this.state = {
            modeler: "",
            status: "?",
            id: "?",
            verificationsVisibility: false,
            modelerVisibility: true,
            launched: false,
            launches: 0,
        };
    }

    async componentDidMount() {
        this.modeler = new BpmnJS({
            container: '#canvas',
            keyboard: {
                bindTo: window
            },
            propertiesPanel: {
                parent: '#properties'
            },
            additionalModules: [
                propertiesPanelModule,
                propertiesProviderModule
            ],
        });
        try {
            const result = await this.modeler.createDiagram();
            const { warnings } = result;
            console.log(warnings);
        } catch (err) {
            console.log(err.message, err.warnings);
        }
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
            const result = await this.modeler.saveXML({ format: true });
            const { xml } = result;
            const xhr = new XMLHttpRequest();
            xhr.open("POST", "http://localhost:5000/verifications");
            xhr.setRequestHeader("Access-Control-Allow-Headers", "*");
            xhr.setRequestHeader("Access-Control-Allow-Origin", "*");
            xhr.setRequestHeader("Content-Type", "application/xml");
            xhr.send(xml);
        } catch (err) {
            console.log(err);
        }
    }

    async launchVerification() {
        this.sendData();
        this.setState({
            launched: true,
        })
        sleep(500).then(() => {
            fetch("http://localhost:5000/verifications/latest")
                .then((res) => res.json())
                .then((data) => {
                    this.setState({
                        id: data.id,
                        status: data.status,
                        launches: this.state.launches + 1
                    });
                });
        })
    }

    statusButtonAction() {
        if (this.state.launched) {
            fetch("http://localhost:5000/verifications/latest")
                .then((res) => res.json())
                .then((data) => {
                    this.setState({
                        status: data.status,
                    });
                });
            if (this.state.status !== "PENDING") {
                this.inverseVisibility();
                //TODO clique sur la ligne correspondante du tableau de verifications
                document.getElementById(`${this.state.id}`).click();
            }
        }
    }

    inverseVisibility() {
        this.setState({
            modelerVisibility: !this.state.modelerVisibility,
            verificationsVisibility: !this.state.verificationsVisibility,
        })
    }

    render = () => {
        return (
            <div>
                <div id="settings">
                    <About></About>
                    <span id="verify"
                        style={this.state.modelerVisibility ? {} : { display: "none" }}
                        onClick={() => { this.launchVerification() }}>{this.state.id}
                    </span>
                    <span id="status"
                        style={this.state.modelerVisibility ? {} : { display: "none" }}
                        onClick={() => { this.statusButtonAction() }}>{this.state.status}
                    </span>
                    <span id="verifications"
                        type="button"
                        style={this.state.modelerVisibility ? {} : { display: "none" }}
                        onClick={() => { this.inverseVisibility(); }}
                    >
                        Verifications
                    </span>
                    <span id="modeler"
                        type="button"
                        style={this.state.verificationsVisibility ? {} : { display: "none" }}
                        onClick={() => { this.inverseVisibility(); }}
                    >
                        Modeler
                    </span>
                </div>
                <div id="modeler" style={this.state.modelerVisibility ? {} : { display: "none" }}>
                    <button id="open" class="button" href="true" onClick={() => {
                        document.getElementById('import-input').click();
                    }}><FaFolderOpen size={iconsSize} /></button>
                    <input id="import-input" onChange={() => {
                        this.displayDiagram(document.getElementById('import-input').files[0]);
                    }} name="files" style={{ display: 'none' }} type="file" accept=".bpmn"></input>
                    <button id="save" class="button" href="true" onClick={() => { this.exportDiagram() }}><FaDownload size={iconsSize} /></button>
                    <button id="new" class="button" href="true" onClick={() => { this.modeler.createDiagram() }}><FaPlus size={iconsSize} /></button>
                    <div id="modeler">
                        <div id="canvas" style={{ width: '75%', height: '98vh', float: 'left' }}></div>
                        <div id="properties" style={{ width: '25%', height: '98vh', float: 'right', maxHeight: '98vh', overflowX: 'auto' }}></div>
                    </div>
                </div>
                <div id="verifications" style={this.state.verificationsVisibility ? {} : { display: "none" }}>
                    <Verifications dataFromParent={this.state.launches} statusLastVerif={this.state.status}></Verifications>
                </div>
            </div >
        )
    }
}

export default BpmnModelerComponent;
