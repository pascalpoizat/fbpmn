from flask import jsonify, Blueprint
from app import app, db
from app.models import Application, Version
from marshmallow import ValidationError
from flask_restplus import Api
from app.resources import ConstraintsById, ConstraintsByVerification, ConstraintsList, CounterExampleById, CounterExampleByResult, CounterExampleList, LatestVerification, ModelByCounterExample, ModelByVerification, ResultById, ResultByVerification, ResultList, UserDefsByVerification, UserPropsById, UserPropsByVerification, UserPropsList, VerificationById, VerificationByResult, VerificationList, models_ns, userdefs_ns, userprops_ns, constraints_ns, verifications_ns, results_ns, counter_examples_ns, ModelList, ModelById, UserDefsList, UserDefsById

URL_ID = "/<int:id>"

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

models_ns.add_resource(ModelList, "")
models_ns.add_resource(ModelById, URL_ID)
userdefs_ns.add_resource(UserDefsList, "")
userdefs_ns.add_resource(UserDefsById, URL_ID)
userprops_ns.add_resource(UserPropsList, "")
userprops_ns.add_resource(UserPropsById, URL_ID)
constraints_ns.add_resource(ConstraintsList, "")
constraints_ns.add_resource(ConstraintsById, URL_ID)
verifications_ns.add_resource(VerificationList, "")
verifications_ns.add_resource(VerificationById, URL_ID)
verifications_ns.add_resource(LatestVerification, "/latest")
verifications_ns.add_resource(
    ModelByVerification, f'{URL_ID}/model')
verifications_ns.add_resource(
    UserDefsByVerification, f'{URL_ID}/userdefs')
verifications_ns.add_resource(
    UserPropsByVerification, f'{URL_ID}/userprops')
verifications_ns.add_resource(
    ConstraintsByVerification, f'{URL_ID}/constraints')
verifications_ns.add_resource(
    ResultByVerification, f'{URL_ID}/results')
results_ns.add_resource(ResultList, "")
results_ns.add_resource(ResultById, URL_ID)
results_ns.add_resource(VerificationByResult, f'{URL_ID}/verification')
results_ns.add_resource(CounterExampleByResult,
                        f'{URL_ID}/counter_example')
counter_examples_ns.add_resource(CounterExampleList, "")
counter_examples_ns.add_resource(CounterExampleById, URL_ID)
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
