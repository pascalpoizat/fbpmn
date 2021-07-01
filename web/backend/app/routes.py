from flask import request, jsonify
import time
from app import app, db
from app.models import Application, Version

a = Application()


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
    models = Application.get_all_models()
    models_json = []
    for m in models:
        m.__dict__['taille'] = len(m.__dict__['content'])
        del m.__dict__['_sa_instance_state'], m.__dict__['content']
        models_json.append(m.__dict__)
    return jsonify(models_json)


@app.route('/verifications', methods=['POST', 'GET'])
def verifications():
    if request.method == 'POST':
        # with request.data only, a b' ' appears to indicate the string is binary
        model = str(request.data.decode('UTF-8'))
        v = a.create_verification()
        m = v.create_model(model)
        workir = v.launch_check(m.name)
        xx = v.results_list(workir, m.name)
        del m, v
        return "tout roule"
    else:
        verifications = Application.get_all_verifications()
        verifications_json = []
        for v in verifications:
            del v.__dict__['_sa_instance_state'], v.__dict__[
                'pub_date'], v.__dict__['status']
            verifications_json.append(v.__dict__)
        return jsonify(verifications_json)


# problèmes avec la sérialization des attributs de classe Enum

@app.route('/results', methods=['GET'])
def get_all_results():
    results = Application.get_all_results()
    results_json = []
    for r in results:
        del r.__dict__['_sa_instance_state'], r.__dict__[
            'communication'], r.__dict__['property']
        results_json.append(r.__dict__)
    return jsonify(results_json)


@app.route('/models/<id>', methods=['GET'])
def get_model_by_id(id):
    m = Application.get_model_by_id(id)
    return jsonify(id=m.id, name=m.name,
                   taille=len(m.content))


@app.route('/verifications/<id>', methods=['GET'])
def get_verification_by_id(id):
    v = Application.get_verification_by_id(id)
    print(len(v.results))
    return jsonify(id=v.id, date=v.pub_date, model=v.model_id, output=v.output, results=f'/results/{v.results[0].id}')


@app.route('/results/<id>', methods=['GET'])
def get_result_by_id(id):
    r = Application.get_result_by_id(id)
    return jsonify(id=r.id, value=r.value, verification=f'verifications/{r.verification.id}')


@app.route('/verifications/<id>/model', methods=['GET'])
def get_model_by_verification(id):
    model_id = (Application.get_verification_by_id(id)).get_model()
    m = get_model_by_id(model_id)
    return jsonify(id=m.id, name=m.name,
                   taille=len(m.content))


@app.route('/verifications/<id>/results', methods=['GET'])
def get_results_by_verification(id):
    verification_id = Application.get_verification_by_id(id)
    # TODO use relationship or a new Application's method


@app.route('/results/<id>/verification', methods=['GET'])
def get_verification_by_result(id):
    verification_id = (Application.get_result_by_id(id)).get_verification()
    v = Application.get_verification_by_id(verification_id)
    return jsonify(id=v.id, status=str(v.status),
                   date=v.pub_date, model=v.model_id)
