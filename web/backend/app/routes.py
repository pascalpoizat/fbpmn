from flask import request, jsonify
from app import app
from app.models import Application, Version
import json

a = Application()


@app.route('/version', methods=['GET'])
def version():
    v = Version()
    version = jsonify(major=v.major, minor=v.minor, patch=v.patch)
    del v
    return version


@app.route('/models', methods=['GET'])
def get_all_models():
    models = a.get_all_models()
    for m in models:
        pass


@app.route('/verifications', methods=['POST', 'GET'])
def verifications():
    if request.method == 'POST':
        # with request.data only, a b' ' appears to indicate the string is binary
        model = str(request.data.decode('UTF-8'))
        m1 = a.create_bpmn_file(model)
        v1 = a.create_verification(m1)
        del m1, v1
    else:
        verifications = a.get_all_verifications()
        for v in verifications:
            pass


@app.route('/results', methods=['GET'])
def get_all_results():
    results = a.get_all_results()
    for r in results:
        pass


@app.route('/model/<id>', methods=['GET'])
def get_model_by_id(id):
    m = a.get_model_by_id(id)
    return jsonify(id=m.id, name=m.name,
                   taille=len(m.content))


@app.route('/verification/<id>', methods=['GET'])
def get_verification_by_id(id):
    v = a.get_verification_by_id(id)
    return jsonify(id=v.id, status=str(v.status),
                   date=v.pub_date, model=v.model_id)


@app.route('/result/<id>', methods=['GET'])
def get_result_by_id(id):
    r = a.get_result_by_id(id)
    return jsonify(id=r.id, communication=r.communication,
                   property=r.property, value=r.value, verification=r.verification_id)


@app.route('/verification/<id>/model', methods=['GET'])
def get_model_by_verification(id):
    model_id = (a.get_verification_by_id(id)).get_model()
    m = a.get_model_by_id(model_id)
    return jsonify(id=m.id, name=m.name,
                   taille=len(m.content))


@app.rout('/verification/<id>/results', methods=['GET'])
def get_results_by_verification(id):
    verification_id = a.get_verification_by_id(id)
    # TODO use relationship or a new Application's method


@app.route('/result/<id>/verification', methods=['GET'])
def get_verification_by_result(id):
    verification_id = (a.get_result_by_id(id)).get_verification()
    v = a.get_verification_by_id(verification_id)
    return jsonify(id=v.id, status=str(v.status),
                   date=v.pub_date, model=v.model_id)
