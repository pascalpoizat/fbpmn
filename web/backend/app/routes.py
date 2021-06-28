from flask import request, jsonify
from app import app
from app.models import Application, Version

a = Application()


@app.route('/version', methods=['GET'])
def version():
    v = Version()
    version = jsonify(major=v.major, minor=v.minor, patch=v.patch)
    del v
    return version


@app.route('/verifications', methods=['POST', 'GET'])
def verifications():
    if request.method == 'POST':
        # with request.data only, a b' ' appears to indicate the string is binary
        model = str(request.data.decode('UTF-8'))
        m1 = a.create_bpmn_file(model)
        v1 = a.create_verification(m1)
        del m1, v1
    else:
        return {'id': 0}
