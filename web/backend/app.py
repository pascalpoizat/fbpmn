from flask import Flask, request, jsonify
from flask_cors import CORS, cross_origin
from flask_mysqldb import MySQL
import subprocess
import os
import re

app = Flask(__name__)

app.config['CORS_HEADERS'] = 'Content-Type'
cors = CORS(app, resources={
            r"/verifications": {"origins": "http://localhost:3000"}})

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
    major = int(version[0])
    minor = int(version[1])
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
            'patch': int(patch[0])}


@app.route('/verifications', methods=['GET', 'POST'])
@cross_origin(origin='localhost', headers=['Content- Type', 'Authorization'])
def verifications():
    if request.method == 'POST':
        # with request.data only, a b' ' appears to indicate the string is binary
        model = str(request.data.decode('UTF-8'))
        name = (re.search(r'<bpmn:collaboration id="(.+)">', model)).group(1)
        # to conserve the "" in the bpmn file
        model_for_file = model.replace('\"', '\\"\"')
        os.system(f'echo "{model_for_file}" > /tmp/{name}.bpmn')
        os.system(f'fbpmn-check /tmp/{name}.bpmn')
        cursor = mysql.connection.cursor()
        cursor.execute(
            f' INSERT INTO Verification (model_name, model, `status`) VALUES (%s,%s,"PENDING") % ({name}, {model})')
        mysql.connection.commit()
        cursor.close()
        # attente fin de vérif
        '''
        cursor.execute(
            " UPDATE Verification VALUES(%d,%d,%d)" % (int(major), int(minor), int(patch[0])))
        mysql.connection.commit()
        '''
        # insertion lignes verificationResults
        # MAJ ligne verifs
        # cursor.close()
        # supprime fichier et dossier temp
        return {'id': 0}
    else:
        return {'id': 0}


@app.route('/verifications/<int:verification_id>}', methods=['GET'])
def verificationsId(verification_id):
    pass
