import React, { Component } from 'react';
import { FaFolderOpen, FaDownload } from 'react-icons/fa';
import BpmnJS from 'bpmn-js/dist/bpmn-modeler.production.min.js';
import 'bpmn-js/dist/assets/diagram-js.css';
import 'bpmn-js/dist/assets/bpmn-font/css/bpmn.css';
import propertiesPanelModule from 'bpmn-js-properties-panel';
import propertiesProviderModule from 'bpmn-js-properties-panel/lib/provider/camunda';
import camundaModdleDescriptor from 'camunda-bpmn-moddle/resources/camunda';
import VerificationDetail from "../VerificationDetail.js";
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

function hideCanvas() {
    let modeler = document.getElementById("modeler");
    modeler.style.display = "none";
}

function showCanvas() {
    let modeler = document.getElementById("modeler");
    modeler.style.display = "block";
}

function showList() {
    let list = document.getElementById("list-verifications");
    list.style.display = "block";
}

function hideList() {
    let list = document.getElementById("list-verifications");
    list.style.display = "none";
}

function showModelerButton() {
    let list = document.getElementById("modeler");
    list.style.display = "block";
}

function hideModelerButton() {
    let list = document.getElementById("modeler");
    list.style.display = "none";
}

function showVerificationsButton() {
    let list = document.getElementById("verifications");
    list.style.display = "block";
}

function hideVerificationsButton() {
    let list = document.getElementById("verifications");
    list.style.display = "none";
}

let id, status;
class BpmnModelerComponent extends Component {

    modeler = null;

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
            moddleExtensions: {
                camunda: camundaModdleDescriptor
            }
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

    render = () => {
        return (
            <div>
                <div id="settings">
                    <About></About>
                    <a id="verify" onClick={() => {
                        this.sendData();
                        fetch("http://localhost:5000/verifications/latest")
                            .then((res) => res.json())
                            .then((data) => {
                                id = data.id
                                status = data.status
                            });
                        var r = document.getElementById('verify');
                        r.innerHTML = id;
                        var s = document.getElementById('status');
                        s.innerHTML = status
                    }}>
                    </a>
                    <a id="status" onClick={() => {
                        fetch("http://localhost:5000/verifications/latest")
                            .then((res) => res.json())
                            .then((data) => {
                                status = data.status
                            });
                        var s = document.getElementById('status');
                        s.innerHTML = status
                    }}></a>
                    <a id="verifications"
                        type="button"
                        style={{ display: "block" }}
                        onClick={() => {
                            {
                                hideCanvas();

                            }
                        }}
                    >
                        Verifications
                    </a>
                    <a id="modeler"
                        type="button"
                        style={{ display: "none" }}
                        onClick={() => {
                            {
                                showCanvas();
                                hideList();
                                hideModelerButton();
                                showVerificationsButton();
                            }
                        }}
                    >
                        Modeler
                    </a>
                </div>
                <div id="modeler" style={{ display: "none" }}>
                    <button id="open" href="true" onClick={() => {
                        document.getElementById('import-input').click();
                    }}><FaFolderOpen size={25} /></button>
                    <input id="import-input" onChange={() => {
                        this.displayDiagram(document.getElementById('import-input').files[0]);
                    }} name="files" style={{ display: 'none' }} type="file" accept=".bpmn"></input>
                    <button id="save" href="true" onClick={() => { this.exportDiagram() }}><FaDownload size={25} /></button>
                    <div id="modeler">
                        <div id="canvas" style={{ width: '75%', height: '98vh', float: 'left' }}></div>
                        <div id="properties" style={{ width: '25%', height: '98vh', float: 'right', maxHeight: '98vh', overflowX: 'auto' }}></div>
                    </div>
                </div>
                <Verifications></Verifications>
            </div >
        )
    }
}

export default BpmnModelerComponent;
