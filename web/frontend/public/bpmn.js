// modeler instance
var bpmnModeler = new BpmnJS({
    container: '#canvas',
    keyboard: {
        bindTo: window
    }
});

bpmnModeler.createDiagram();

/**
 * Save diagram contents and offer to download it.
 */
function exportDiagram() {
    bpmnModeler.saveXML({ format: true }, function (err, xml) {

        if (err) {
            return console.error('could not save BPMN 2.0 diagram', err);
        }
        save("diagram.bpmn", xml);
    });
}

/**
 * offer to download a file.
 * @param {String} filename name of the file
 * @param {String} data data contained in the file
 */
function save(filename, data) {
    var blob = new Blob([data], { type: 'text/xml' });
    if (window.navigator.msSaveOrOpenBlob) {
        window.navigator.msSaveBlob(blob, filename);
    }
    else {
        var elem = window.document.createElement('a');
        elem.href = window.URL.createObjectURL(blob);
        elem.download = filename;
        document.body.appendChild(elem);
        elem.click();
        document.body.removeChild(elem);
    }
}

/**
 * Open diagram from string in our modeler instance.
 *
 * @param {String} bpmnXML diagram to display
 */
function openDiagram(bpmnXML) {
    // import diagram
    bpmnModeler.importXML(bpmnXML, function (err) {
        if (err) {
            return console.error('could not import BPMN 2.0 diagram', err);
        }
    });
}

/**
 * Open diagram from file in our modeler instance.
 *
 * @param {File} DiagramFile diagram to display
 */
function displayDiagram(DiagramFile) {
    let reader = new FileReader();
    reader.readAsText(DiagramFile);
    reader.onload = function (event) { openDiagram(event.target.result) };
}
