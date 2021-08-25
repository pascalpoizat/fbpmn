from os import error
from flask import request, jsonify, Blueprint
from app import app, db
from app.models import Application, Constraints, CounterExample, Model, UserDefs, UserProps, Verification, Result, Version, get_workdir
from app.schemas import ConstraintsSchema, CounterExampleSchema, ModelSchema, ResultSchema, UserDefsSchema, UserPropsSchema, VerificationSchema
from marshmallow import ValidationError
from flask_restplus import Api
from app.resources import *


a = Application()

blue_print = Blueprint('api', __name__, url_prefix='/api')
api = Api(blue_print, doc='/doc', title='Documentation of fBPMN API')
app.register_blueprint(blue_print)

api.add_namespace(models_ns)
api.add_namespace(userdefs_ns)
api.add_namespace(userprops_ns)
api.add_namespace(constraints_ns)
api.add_namespace(verifications_ns)
api.add_namespace(results_ns)
api.add_namespace(counter_examples_ns)

models_ns.add_resource(ModelListResource, "")
models_ns.add_resource(ModelByIdResource, "/<int:id>")
userdefs_ns.add_resource(UserDefsListResource, "")
userdefs_ns.add_resource(UserDefsByIdResource, "/<int:id>")
userprops_ns.add_resource(UserPropsListResource, "")
userprops_ns.add_resource(UserPropsByIdResource, "/<int:id>")
constraints_ns.add_resource(ConstraintsListResource, "")
constraints_ns.add_resource(ConstraintsByIdResource, "/<int:id>")
verifications_ns.add_resource(VerificationListResource, "")
verifications_ns.add_resource(VerificationByIdResource, "/<int:id>")
verifications_ns.add_resource(LatestVerificationResource, "/latest")
verifications_ns.add_resource(
    ModelByVerification, "/<int:id>/model")
verifications_ns.add_resource(
    UserDefsByVerificationResource, "/<int:id>/userdefs")
verifications_ns.add_resource(
    UserPropsByVerificationResource, "/<int:id>/userprops")
verifications_ns.add_resource(
    ConstraintsByVerificationResource, "/<int:id>/constraints")
verifications_ns.add_resource(
    ResultByVerificationResource, "/<int:id>/results")
results_ns.add_resource(ResultListResource, "")
results_ns.add_resource(ResultByIdResource, "/<int:id>")
results_ns.add_resource(VerificationByResult, "/<int:id>/verification")
results_ns.add_resource(CounterExampleResourceByResult,
                        "/<int:id>/counter_example")
counter_examples_ns.add_resource(CounterExampleListResource, "")
counter_examples_ns.add_resource(CounterExampleByIdResource, "/<int:id>")
counter_examples_ns.add_resource(ModelByCounterExample, "/<int:id>/model")


@api.errorhandler(ValidationError)
def handle_validation_error(error):
    return jsonify(error.messages), 400


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
    models = a.get_all_elements(Model)
    return (create_schema(ModelSchema, True)).jsonify(models)


@app.route('/userdefs', methods=['POST', 'GET'])
def get_all_userdefs():
    ud = a.get_all_elements(UserDefs)
    return (create_schema(UserDefsSchema, True)).jsonify(ud)


@app.route('/userprops', methods=['POST', 'GET'])
def get_all_userprops():
    up = a.get_all_elements(UserProps)
    return (create_schema(UserPropsSchema, True)).jsonify(up)


@app.route('/constraints', methods=['POST', 'GET'])
def get_all_constraints():
    c = a.get_all_elements(Constraints)
    return (create_schema(ConstraintsSchema, True)).jsonify(c)


@app.route('/verifications', methods=['POST', 'GET'])
def verifications():
    if request.method == 'POST':
        data = request.get_json()
        model = (data['model']['xml'])
        userdefs = data['userdefs']
        userprops = data['userprops']
        constraint = str(f'CONSTANT ConstraintNode <- {data["constraintNode"]}\n'
                         f'         ConstraintEdge <- {data["constraintEdge"]}\n'
                         "         Constraint <- ConstraintNodeEdge\n")
        v = a.create_verification()
        try:
            m = v.create_model(model)
            v.create_file(UserDefs, userdefs, m.name)
            v.create_file(UserProps, userprops, m.name)
            v.create_file(Constraints, constraint, m.name)
            output = v.launch_check(m.name)
            workdir = get_workdir(output)
            xx = v.create_results_list(workdir, m.name)
            v.create_counter_examples(workdir, m.name, xx)
            del m, v
            return output
        except (AttributeError, TypeError) as e:
            print(e)
            v.aborted()
            return ("Incorrect model")
    else:
        v = a.get_all_elements(Verification)
        return (create_schema(VerificationSchema, True)).jsonify(v)


@app.route('/results', methods=['GET'])
def get_all_results():
    r = a.get_all_elements(Result)
    return (create_schema(ResultSchema, True)).jsonify(r)


@app.route('/counter_examples', methods=['GET'])
def get_all_counter_examples():
    ce = a.get_all_elements(CounterExample)
    return (create_schema(CounterExampleSchema, True)).jsonify(ce)


@app.route('/models/<id>', methods=['GET'])
def get_model_by_id(id):
    m = a.get_element_by_id(Model, id)
    return (create_schema(ModelSchema, False)).jsonify(m)


@app.route('/userdefs/<id>', methods=['GET'])
def get_userdefs_by_id(id):
    ud = a.get_element_by_id(UserDefs, id)
    return (create_schema(UserDefsSchema, False)).jsonify(ud)


@app.route('/userprops/<id>', methods=['GET'])
def get_userprops_by_id(id):
    up = a.get_element_by_id(UserProps, id)
    return (create_schema(UserPropsSchema, False)).jsonify(up)


@app.route('/constraints/<id>', methods=['GET'])
def get_constraints_by_id(id):
    c = a.get_element_by_id(Constraints, id)
    return (create_schema(ConstraintsSchema, False)).jsonify(c)


@app.route('/verifications/<id>', methods=['GET'])
def get_verification_by_id(id):
    v = a.get_element_by_id(Verification, id)
    return (create_schema(VerificationSchema, False)).jsonify(v)


@app.route('/verifications/<id>', methods=['DELETE'])
def delete_verification(id):
    v = Verification.query.get(id)
    db.session.delete(v)
    db.session.commit()
    return "Verification was successfully deleted"


@app.route('/verifications/latest', methods=['GET'])
def get_latest_verification():
    v = a.get_latest_verification()
    return (create_schema(VerificationSchema, False)).jsonify(v)


@app.route('/results/<id>', methods=['GET'])
def get_result_by_id(id):
    r = a.get_element_by_id(Result, id)
    return (create_schema(ResultSchema, False)).jsonify(r)


@app.route('/counter_examples/<id>', methods=['GET'])
def get_counter_examples_by_id(id):
    ce = a.get_element_by_id(CounterExample, id)
    return (create_schema(CounterExampleSchema, False)).jsonify(ce)


@app.route('/verifications/<id>/model', methods=['GET'])
def get_model_by_verification(id):
    model_id = (a.get_element_by_id(Verification, id)).model_id
    return get_model_by_id(model_id)


@app.route('/verifications/<id>/userdefs', methods=['GET'])
def get_userdefs_by_verification(id):
    userdefs_id = (a.get_element_by_id(Verification, id)).userdefs.id
    return get_userdefs_by_id(userdefs_id)


@app.route('/verifications/<id>/userprops', methods=['GET'])
def get_userprops_by_verification(id):
    userprops_id = (a.get_element_by_id(Verification, id)).userprops.id
    return get_userprops_by_id(userprops_id)


@app.route('/verifications/<id>/constraints', methods=['GET'])
def get_constraints_by_verification(id):
    constraints_id = (a.get_element_by_id(Verification, id)).constraints.id
    return get_constraints_by_id(constraints_id)


@app.route('/verifications/<id>/results', methods=['GET'])
def get_results_by_verification(id):
    verification = a.get_element_by_id(Verification, id)
    return (create_schema(ResultSchema, True)).jsonify(verification.results)


@app.route('/verifications/<id>/value', methods=['GET'])
def get_value_by_verification(id):
    verification = a.get_element_by_id(Verification, id)
    return verification.get_value()


# manque ces tois dernières
@app.route('/results/<id>/verification', methods=['GET'])
def get_verification_by_result(id):
    verification = (a.get_element_by_id(Result, id)).verification
    return (create_schema(VerificationSchema, False)).jsonify(verification)


@app.route('/results/<id>/counter_example', methods=['GET'])
def get_counter_example_from_result(id):
    counter_example = (a.get_element_by_id(Result, id)).counter_example
    if counter_example:
        return (create_schema(CounterExampleSchema, False)).jsonify(counter_example)
    else:
        return "Record not found", 400


@app.route('/counter_examples/<id>/model', methods=['GET'])
def get_model_from_counter_example(id):
    ce = a.get_element_by_id(CounterExample, id)
    m_id = ce.get_result().get_verification().model_id
    return get_model_by_id(m_id)


@app.errorhandler(Exception)
def basic_error(e):
    return "an error occured: " + str(e)
