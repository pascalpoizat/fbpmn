from flask import request, jsonify
from app import app, db
from app.models import Application, Verification, Version, Model, Result, get_workir_with_output
from app.context import Communication, Property

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
        m = Model(model)
        db.session.add(m)
        a.create_verification()

    else:
        return {'id': 0}


@app.route('/verifications/<int:verification_id>}', methods=['GET'])
def verificationsId(verification_id):
    pass
