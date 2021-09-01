from flask import jsonify, Blueprint
from app import app, db
from app.models import Application, Version
from marshmallow import ValidationError
from flask_restplus import Api
from app.resources import CounterExampleById, CounterExampleByResult, CounterExampleList, LatestVerification, ModelByCounterExample, ModelByVerification, \
    ResultById, ResultByVerification, ResultList, VerificationById, VerificationByResult, VerificationList, models_ns, verifications_ns, results_ns, counter_examples_ns, ModelList, ModelById

URL_ID = "/<int:id>"

a = Application()

blue_print = Blueprint('api', __name__, url_prefix='/api')
api = Api(blue_print, doc='/doc', title='Documentation of fBPMN API')
app.register_blueprint(blue_print)

api.add_namespace(models_ns)
api.add_namespace(verifications_ns)
api.add_namespace(results_ns)
api.add_namespace(counter_examples_ns)

models_ns.add_resource(ModelList)
models_ns.add_resource(ModelById)
verifications_ns.add_resource(VerificationList)
verifications_ns.add_resource(VerificationById)
verifications_ns.add_resource(LatestVerification)
verifications_ns.add_resource(ModelByVerification)
verifications_ns.add_resource(ResultByVerification)
results_ns.add_resource(ResultList)
results_ns.add_resource(ResultById)
results_ns.add_resource(VerificationByResult)
results_ns.add_resource(CounterExampleByResult)
counter_examples_ns.add_resource(CounterExampleList)
counter_examples_ns.add_resource(CounterExampleById)
counter_examples_ns.add_resource(ModelByCounterExample)


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
