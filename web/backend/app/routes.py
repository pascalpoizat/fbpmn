from flask import request, jsonify
from app import app, db
from app.models import Application, CounterExample, Model, Verification, Result, Version, get_workdir

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
            v.__dict__['status'] = str(v.status.name)
            v.__dict__['model'] = f'/models/{v.model_id}'
            v.__dict__['results'] = results_json
            v.__dict__['pub_date'] = v.pub_date.strftime("%b/%d/%Y %H:%M:%S")
            del v.__dict__['_sa_instance_state'], v.__dict__['model_id']
            verifications_json.append(v.__dict__)
        return jsonify(verifications_json)
    if type(list[0]) == Result:
        results_json = []
        for r in list:
            r.__dict__['communication'] = str(r.communication.name)
            r.__dict__['property'] = str(r.property.name)
            if not r.value:
                r.__dict__[
                    'counter_example_id'] = r.counter_example.first().id
            else:
                r.__dict__['counter_example_id'] = None
            r.__dict__[
                'verification'] = f'verifications/{r.verification_id}'
            del r.__dict__['_sa_instance_state'], r.__dict__['verification_id']
            results_json.append(r.__dict__)
        return jsonify(results_json)
    if type(list[0]) == CounterExample:
        counter_examples_json = []
        for ce in list:
            ce.__dict__['result'] = f'/results/{ce.result_id}'
            del ce.__dict__['_sa_instance_state'], ce.__dict__['result_id']
            counter_examples_json.append(ce.__dict__)
        return jsonify(counter_examples_json)


def serialize_object(object):
    if type(object) == Model:
        return jsonify(id=object.id, name=object.name,
                       content=object.content, verification=f'/verifications/{object.verification[0].id}')
    if type(object) == Verification:
        results_json = []
        for r in object.results:
            results_json.append(f'/results/{r.id}')
        return jsonify(id=object.id, status=str(object.status.name),
                       pub_date=object.pub_date, duration=object.duration, model=f'models/{object.model_id}', output=object.output, results=results_json)
    if type(object) == Result:
        if not object.value:
            return jsonify(id=object.id, communication=str(object.communication.name),
                           property=str(object.property.name), value=object.value, counter_example_id=object.counter_example.first().id, verification=f'verifications/{object.verification.id}')
        else:
            return jsonify(id=object.id, communication=str(object.communication.name),
                           property=str(object.property.name), value=object.value, counter_example_id=None, verification=f'verifications/{object.verification.id}')
    if type(object) == CounterExample:
        return jsonify(lcex=object.lcex, lstatus=object.lstatus, lname=object.lname, lmodel=object.lmodel, result=f'/results/{object.result_id}')


@app.before_first_request
def before_first_request_func():
    db.create_all()


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
        try:
            m = v.create_model(model)
            output = v.launch_check(m.name)
            workdir = get_workdir(output)
            xx = v.create_results_list(workdir, m.name)
            v.create_counter_examples(workdir, m.name, xx)
            del m, v
            return output
        except (AttributeError, TypeError):
            v.aborted()
            return ("Incorrect model")
    else:
        verifications = a.get_all_verifications()
        return serialize_list(verifications)


@app.route('/results', methods=['GET'])
def get_all_results():
    results = a.get_all_results()
    return serialize_list(results)


@app.route('/counter_examples', methods=['GET'])
def get_all_counter_examples():
    counter_examples = a.get_all_counter_examples()
    return serialize_list(counter_examples)


@app.route('/models/<id>', methods=['GET'])
def get_model_by_id(id):
    m = a.get_model_by_id(id)
    return serialize_object(m)


@app.route('/verifications/<id>', methods=['GET'])
def get_verification_by_id(id):
    v = a.get_verification_by_id(id)
    return serialize_object(v)


@app.route('/verifications/<id>', methods=['DELETE'])
def delete_verification(id):
    v = Verification.query.get(id)
    db.session.delete(v)
    db.session.commit()
    return "Verification was successfully deleted"


@app.route('/verifications/latest', methods=['GET'])
def get_latest_verification():
    v = a.get_latest_verification()
    return serialize_object(v)


@app.route('/results/<id>', methods=['GET'])
def get_result_by_id(id):
    r = a.get_result_by_id(id)
    return serialize_object(r)


@app.route('/counter_examples/<id>', methods=['GET'])
def get_counter_examples_by_id(id):
    ce = a.get_counter_example_by_id(id)
    return serialize_object(ce)


@app.route('/verifications/<id>/model', methods=['GET'])
def get_model_by_verification(id):
    model_id = (a.get_verification_by_id(id)).model_id
    return get_model_by_id(model_id)


@app.route('/verifications/<id>/results', methods=['GET'])
def get_results_by_verification(id):
    verification = a.get_verification_by_id(id)
    return serialize_list(verification.results)


@app.route('/verifications/<id>/value', methods=['GET'])
def get_value_by_verification(id):
    verification = a.get_verification_by_id(id)
    return verification.get_value()


@app.route('/results/<id>/verification', methods=['GET'])
def get_verification_by_result(id):
    verification_id = (a.get_result_by_id(id)).verification_id
    v = a.get_verification_by_id(verification_id)
    return serialize_object(v)


@app.route('/results/<id>/counter_example', methods=['GET'])
def get_counter_example_from_result(id):
    return serialize_object((a.get_result_by_id(id)).get_counter_example())


@app.route('/counter_examples/<id>/model', methods=['GET'])
def get_model_from_counter_example(id):
    ce = a.get_counter_example_by_id(id)
    m_id = ce.get_result().get_verification().model_id
    m = a.get_model_by_id(m_id)
    return serialize_object(m)


@app.errorhandler(Exception)
def basic_error(e):
    return "an error occured: " + str(e)
