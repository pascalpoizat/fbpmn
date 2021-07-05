from flask import request, jsonify
import time
from app import app, db
from app.models import Application, Version, get_workdir

a = Application()

# TODO refactorer -> une fonction serialize() pour éviter répétition de jsonify


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
    models = Application.get_all_models()
    models_json = []
    for m in models:
        m.__dict__['taille'] = len(m.__dict__['content'])
        m.__dict__['verification'] = f'/verifications/{m.verification[0].id}'
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
        output = v.launch_check(m.name)
        workdir = get_workdir(output)
        xx = v.results_list(workdir, m.name)
        del m, v
        return output
    else:
        verifications = Application.get_all_verifications()
        verifications_json = []
        for v in verifications:
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


# problèmes avec la sérialization des attributs de classe Enum

@app.route('/results', methods=['GET'])
def get_all_results():
    results = Application.get_all_results()
    results_json = []
    for r in results:
        del r.__dict__['_sa_instance_state']
        r.__dict__['communication'] = str(r.communication.name)
        r.__dict__['property'] = str(r.property.name)
        r.__dict__['verification_id'] = f'verifications/{r.verification_id}'
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
    results_json = []
    for r in v.results:
        results_json.append(f'/results/{r.id}')
    return jsonify(id=v.id, status=str(v.status.name),
                   date=v.pub_date, model=f'models/{v.model.id}', output=v.output, results=results_json)


@app.route('/results/<id>', methods=['GET'])
def get_result_by_id(id):
    r = Application.get_result_by_id(id)
    return jsonify(id=r.id, communication=str(r.communication.name),
                   property=str(r.property.name), value=r.value, verification=f'verifications/{r.verification.id}')


@app.route('/verifications/<id>/model', methods=['GET'])
def get_model_by_verification(id):
    model_id = (Application.get_verification_by_id(id)).get_model()
    return get_model_by_id(model_id)


@app.route('/verifications/<id>/results', methods=['GET'])
def get_results_by_verification(id):
    verification = Application.get_verification_by_id(id)
    results_json = []
    for r in verification.results:
        del r.__dict__['_sa_instance_state']
        r.__dict__['communication'] = str(r.communication.name)
        r.__dict__['property'] = str(r.property.name)
        r.__dict__['verification_id'] = f'verifications/{r.verification_id}'
        results_json.append(r.__dict__)
    return jsonify(results_json)


@app.route('/results/<id>/verification', methods=['GET'])
def get_verification_by_result(id):
    verification_id = (Application.get_result_by_id(id)).get_verification()
    v = Application.get_verification_by_id(verification_id)
    return jsonify(id=v.id, status=str(v.status.name),
                   date=v.pub_date, model=v.model_id)
