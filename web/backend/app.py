from flask import Flask, jsonify, request
from flask_cors import CORS, cross_origin
from flask_mysqldb import MySQL
import subprocess
import os

app = Flask(__name__)

app.config['CORS_HEADERS'] = 'Content-Type'
cors = CORS(app, resources={r"/*": {"origins": "*"}})

app.config['MYSQL_HOST'] = 'localhost'
app.config['MYSQL_USER'] = 'root'
app.config['MYSQL_PASSWORD'] = 'Malinva5d'
app.config['MYSQL_DB'] = 'fBPMN_db'
mysql = MySQL(app)


@app.route('/version', methods=['GET'])
def version():
    version = subprocess.check_output(
        "fbpmn version", shell=True, universal_newlines=True)
    version = version.split('.')
    major = version[0]
    minor = version[1]
    patch = version[2].splitlines()
    # insertion dans db
    '''
    cursor = mysql.connection.cursor()
    cursor.execute(
        " INSERT INTO Version VALUES(%d,%d,%d)" % (int(major), int(minor), int(patch[0])))
    mysql.connection.commit()
    cursor.close()
    '''
    return {'major': major,
            'minor': minor,
            'patch': patch[0]}


@app.route('/verifications', methods=['GET', 'POST'])
@cross_origin()
def verifications():
    if request.method == 'POST':
        model = (request.json['model'])
        # to conserve the "" in the bpmn file
        model_for_file = model.replace('\"', '\\"\"')
        os.system(f'echo "{model_for_file}" > /tmp/e033MBE.bpmn')
        id = 12
        ref = 0
        results = 1
        os.system("fbpmn-check /tmp/e033MBE.bpmn")
        return {'id': id,
                'ref': ref,
                'model': model,
                'results': results}
    else:
        return {'id': 0}


@app.route('/verifications/<int:verification_id>}', methods=['GET'])
def verificationsId(verification_id):
    pass
