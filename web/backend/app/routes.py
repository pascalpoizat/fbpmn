from flask import request, jsonify
import time
from app import app, db
from app.models import Application, Model, Verification, Result, Version, get_workdir

a = Application()


def serialize_list(list):
    if type(list[0]) == Model:
        models_json = []
        for m in list:
            m.__dict__['taille'] = len(m.__dict__['content'])
            m.__dict__[
                'verification'] = f'/verifications/{m.verification[0].id}'
            del m.__dict__['_sa_instance_state'], m.__dict__['content']
            models_json.append(m.__dict__)
        return jsonify(models_json)
    if type(list[0]) == Verification:
        verifications_json = []
        for v in list:
            results_json = []
            for r in v.results:
                results_json.append(f'/results/{r.id}')
            del v.__dict__['_sa_instance_state'], v.__dict__[
                'pub_date']
            v.__dict__['status'] = str(v.status.name)
            v.__dict__['model_id'] = f'/models/{v.model_id}'
            v.__dict__['results'] = results_json
            verifications_json.append(v.__dict__)
        return jsonify(verifications_json)
    if type(list[0]) == Result:
        results_json = []
        for r in list:
            del r.__dict__['_sa_instance_state']
            r.__dict__['communication'] = str(r.communication.name)
            r.__dict__['property'] = str(r.property.name)
            r.__dict__[
                'verification_id'] = f'verifications/{r.verification_id}'
            results_json.append(r.__dict__)
        return jsonify(results_json)


def serialize_object(object):
    if type(object) == Model:
        return jsonify(id=object.id, name=object.name,
                       taille=len(object.content))
    if type(object) == Verification:
        results_json = []
        for r in object.results:
            results_json.append(f'/results/{r.id}')
        return jsonify(id=object.id, status=str(object.status.name),
                       date=object.pub_date, model=f'models/{object.model_id}', output=object.output, results=results_json)
    if type(object) == Result:
        return jsonify(id=object.id, communication=str(object.communication.name),
                       property=str(object.property.name), value=object.value, verification=f'verifications/{object.verification.id}')


@app.before_first_request
def before_first_request_func():
    db.create_all()


@app.route('/api/time')
def get_current_time():
    return {'time': time.time()}


@app.route('/version', methods=['GET'])
def version():
    v = Version()
    version = jsonify(major=v.major, minor=v.minor, patch=v.patch)
    del v
    return version


@app.route('/models', methods=['GET'])
def get_all_models():
    models = a.get_all_models()
    return serialize_list(models)


@app.route('/verifications', methods=['POST', 'GET'])
def verifications():
    if request.method == 'POST':
        # with request.data only, a b' ' appears to indicate the string is binary
        model = str(request.data.decode('UTF-8'))
        v = a.create_verification()
        m = v.create_model(model)
        output = v.launch_check(m.name)
        workdir = get_workdir(output)
        xx = v.results_list(workdir, m.name)
        del m, v
        return output
    else:
        verifications = a.get_all_verifications()
        return serialize_list(verifications)


@app.route('/results', methods=['GET'])
def get_all_results():
    results = a.get_all_results()
    return serialize_list(results)


@app.route('/models/<id>', methods=['GET'])
def get_model_by_id(id):
    m = a.get_model_by_id(id)
    return serialize_object(m)


@app.route('/verifications/<id>', methods=['GET'])
def get_verification_by_id(id):
    v = a.get_verification_by_id(id)
    return serialize_object(v)


@app.route('/verifications/latest', methods=['GET'])
def get_latest_verification():
    v = a.get_latest_verification()
    return serialize_object(v)


@app.route('/results/<id>', methods=['GET'])
def get_result_by_id(id):
    r = a.get_result_by_id(id)
    return serialize_object(r)


@app.route('/verifications/<id>/model', methods=['GET'])
def get_model_by_verification(id):
    model_id = (a.get_verification_by_id(id)).get_model()
    return get_model_by_id(model_id)


@app.route('/verifications/<id>/results', methods=['GET'])
def get_results_by_verification(id):
    verification = a.get_verification_by_id(id)
    return serialize_list(verification.results)


@app.route('/results/<id>/verification', methods=['GET'])
def get_verification_by_result(id):
    verification_id = (a.get_result_by_id(id)).get_verification()
    v = a.get_verification_by_id(verification_id)
    return serialize_object(v)
