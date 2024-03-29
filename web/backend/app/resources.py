from flask import request
from flask_restplus import Resource, fields, Namespace
from app import db
from app.models import Application, Constraints, CounterExample, Model, Result, UserNets, UserProps, \
    Verification, get_workdir
from app.schemas import CounterExampleSchema, ModelSchema, ResultSchema, VerificationSchema

MODEL_NOT_FOUND = "Model not found."
VERIFICATION_NOT_FOUND = "Verification not found."
RESULT_NOT_FOUND = "Result not found."
COUNTER_EXAMPLE_NOT_FOUND = "Counter-example not found."

URL_ID = "/<int:id>"


def create_schema(schema_type, bool):
    if bool:
        return schema_type(many=bool)
    else:
        return schema_type()


a = Application()

models_ns = Namespace('models', description='models related operations')
verifications_ns = Namespace(
    'verifications', description='verifications related operations')
results_ns = Namespace('results', description='results related operations')
counter_examples_ns = Namespace(
    'counter_examples', description='counter-examples related operations')

verification_input = verifications_ns.model(
    'Verification', {
        'model': fields.Raw(),
        'usernets': fields.List(fields.String, description='Network01Bag'),
        'userdefs': fields.List(fields.String, description='User1'),
        'userprops': fields.List(fields.String, description='MessageSound'),
        'constraintNode': fields.String('TRUE'),
        'constraintEdge': fields.String('TRUE')
    })


@models_ns.route('')
class ModelList(Resource):
    def get(self):
        models = a.get_all_elements(Model)
        return (create_schema(ModelSchema, True)).jsonify(models)


@models_ns.route(f'{URL_ID}')
class ModelById(Resource):
    def get(self, id):
        m = a.get_element_by_id(Model, id)
        if m:
            return (create_schema(ModelSchema, False)).jsonify(m)
        return {'message': MODEL_NOT_FOUND}, 404


@verifications_ns.route(f'{URL_ID}/model')
class ModelByVerification(Resource):
    def get(self, id):
        model_id = (a.get_element_by_id(Verification, id)).model_id
        return ModelById.get(self, model_id)


@counter_examples_ns.route(f'{URL_ID}/model')
class ModelByCounterExample(Resource):
    def get(self, id):
        ce = a.get_element_by_id(CounterExample, id)
        m_id = ce.get_result().get_verification().model_id
        return ModelById.get(self, m_id)


@verifications_ns.route('')
class VerificationList(Resource):
    def get(self):
        v = a.get_all_elements(Verification)
        return (create_schema(VerificationSchema, True)).jsonify(v)

    @verifications_ns.expect(verification_input)
    def post(self):
        data = request.get_json()
        model = (data['model']['xml'])
        usernets = data['usernets']
        userdefs = data['userdefs']
        userprops = data['userprops']
        constraints = str(f'CONSTANT ConstraintNode <- {data["constraintNode"]}\n'
                          f'         ConstraintEdge <- {data["constraintEdge"]}\n'
                          "         Constraint <- ConstraintNodeEdge\n")
        v = a.create_verification()
        try:
            m = v.create_model(model)
            v.create_file(UserNets, usernets, m.name)
            if not userdefs is None:
                v.create_properties_files(userdefs, userprops, m.name)
            else:
                v.create_file(UserProps, userprops, m.name)
            v.create_file(Constraints, constraints, m.name)
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


@verifications_ns.route(f'{URL_ID}')
class VerificationById(Resource):
    def get(self, id):
        v = a.get_element_by_id(Verification, id)
        if v:
            return (create_schema(VerificationSchema, False)).jsonify(v)
        return {'message': VERIFICATION_NOT_FOUND}, 404

    def delete(self, id):
        v = Verification.query.get(id)
        db.session.delete(v)
        db.session.commit()
        return "Verification was successfully deleted"


@results_ns.route(f'{URL_ID}/verification')
class VerificationByResult(Resource):
    def get(self, id):
        verification = (a.get_element_by_id(Result, id)).verification
        return (create_schema(VerificationSchema, False)).jsonify(verification)


@verifications_ns.route(f'/latest')
class LatestVerification(Resource):
    def get(self):
        v = a.get_latest_verification()
        return (create_schema(VerificationSchema, False)).jsonify(v)


@results_ns.route('')
class ResultList(Resource):
    def get(self):
        r = a.get_all_elements(Result)
        return (create_schema(ResultSchema, True)).jsonify(r)


@results_ns.route(f'{URL_ID}')
class ResultById(Resource):
    def get(self, id):
        r = a.get_element_by_id(Result, id)
        if r:
            return (create_schema(ResultSchema, False)).jsonify(r)
        return {'message': RESULT_NOT_FOUND}, 404


@verifications_ns.route(f'{URL_ID}/results')
class ResultByVerification(Resource):
    def get(self, id):
        verification = a.get_element_by_id(Verification, id)
        return (create_schema(ResultSchema, True)).jsonify(verification.results)


@counter_examples_ns.route('')
class CounterExampleList(Resource):
    def get(self):
        ce = a.get_all_elements(CounterExample)
        return (create_schema(CounterExampleSchema, True)).jsonify(ce)


@counter_examples_ns.route(f'{URL_ID}')
class CounterExampleById(Resource):
    def get(self, id):
        ce = a.get_element_by_id(CounterExample, id)
        if ce:
            return (create_schema(CounterExampleSchema, False)).jsonify(ce)
        return {'message': COUNTER_EXAMPLE_NOT_FOUND}, 404


@results_ns.route(f'{URL_ID}/counter_examples')
class CounterExampleByResult(Resource):
    def get(self, id):
        counter_example = (a.get_element_by_id(Result, id)).counter_example
        if counter_example:
            return (create_schema(CounterExampleSchema, False)).jsonify(counter_example)
        else:
            return "Record not found", 400
