import subprocess
from flask import Flask

app = Flask(__name__)


@app.route('/version', methods=['GET'])
def get_current_version():
    version = subprocess.check_output(
        "fbpmn version", shell=True, universal_newlines=True)
    return {'version': version}


@app.route('/verif', methods=['GET'])
def get_verification():
    # TODO -> diagram = exportation du modèle en cours
    diagram = "fbpmn/models/bpmn-origin/src/e001ClientSupplier.bpmn"
    verification = subprocess.check_output(
        "fbpmn-check %s" % diagram, shell=True, universal_newlines=True)
    return {'version': verification}
