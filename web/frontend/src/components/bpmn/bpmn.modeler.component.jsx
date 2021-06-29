import React, { Component } from 'react';
import BpmnJS from 'bpmn-js/dist/bpmn-modeler.production.min.js';
import 'bpmn-js/dist/assets/diagram-js.css';
import 'bpmn-js/dist/assets/bpmn-font/css/bpmn.css';
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

class BpmnModelerComponent extends Component {

    modeler = null;

    componentDidMount = () => {
        this.modeler = new BpmnJS({
            container: '#canvas',
            keyboard: {
                bindTo: window
            }
        });
        this.modeler.createDiagram();
    }

    exportDiagram = () => {
        this.modeler.saveXML({ format: true }, function (err, xml) {
            if (err) {
                return console.error("could not save BPMN 2.0 diagram", err);
            }
            save("diagram.bpmn", xml);
        });
    }

    openDiagram = (xml) => {
        this.modeler.importXML(xml, function (err) {
            if (err) {
                return console.error("could not import BPMN 2.0 diagram", err);
            }
        });
    }

    displayDiagram(DiagramFile) {
        let reader = new FileReader();
        reader.readAsText(DiagramFile);
        reader.onload = function (event) {
            this.openDiagram(event.target.result);
        };
    }

    render = () => {
        return (
            <div>
                <button id="open" href onClick={() => {
                    document.getElementById('import-input').click();
                }}>Open</button>
                <input id="import-input" onClick={() => {
                    this.displayDiagram(this.files[0]); return false;
                }} name="files" style={{ display: 'none' }} type="file" accept=".bpmn"></input>
                <a id="save" href onClick={this.exportDiagram}>Save</a>
                <div id="canvas" style={{ width: '100%', height: '94vh' }}></div>
            </div >
        )
    }
}

export default BpmnModelerComponent;