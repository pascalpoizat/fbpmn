from flask import request, jsonify
from flask_restplus import Resource, fields, Namespace

from app.models import *
from app.schemas import *

MODEL_NOT_FOUND = "Model not found."
USERDEFS_NOT_FOUND = "Userdefs not found."
VERIFICATION_NOT_FOUND = "Verification not found."


def create_schema(schema_type, bool):
    if bool:
        return schema_type(many=bool)
    else:
        return schema_type()


a = Application()

models_ns = Namespace('models', description='models related operations')
userdefs_ns = Namespace('userdefs', description='userdefs related operations')
userprops_ns = Namespace(
    'userprops', description='userprops related operations')
constraints_ns = Namespace(
    'constraints', description='constraints related operations')
verifications_ns = Namespace(
    'verifications', description='verifications related operations')
results_ns = Namespace('results', description='results related operations')
counter_examples_ns = Namespace(
    'counter_examples', description='counter-examples related operations')


model = models_ns.model('Model', {
    'content': fields.String('Content of the model'),
    'id': fields.Integer,
    'name': fields.String('Name of the model'),
    'verification': fields.String('URL to the verification')
})


class ModelListResource(Resource):
    def get(self):
        models = a.get_all_elements(Model)
        return (create_schema(ModelSchema, True)).jsonify(models)


class ModelByIdResource(Resource):
    def get(self, id):
        m = a.get_element_by_id(Model, id)
        if m:
            return (create_schema(ModelSchema, False)).jsonify(m)
        return {'message': MODEL_NOT_FOUND}, 404


class ModelByVerification(Resource):
    def get(self, id):
        model_id = (a.get_element_by_id(Verification, id)).model_id
        return ModelByIdResource.get(self, model_id)


class ModelByCounterExample(Resource):
    def get(self, id):
        ce = a.get_element_by_id(CounterExample, id)
        m_id = ce.get_result().get_verification().model_id
        return ModelByIdResource.get(self, m_id)


class UserDefsListResource(Resource):
    def get(self):
        ud = a.get_all_elements(UserDefs)
        return (create_schema(UserDefsSchema, True)).jsonify(ud)


class UserDefsByIdResource(Resource):
    def get(self, id):
        ud = a.get_element_by_id(UserDefs, id)
        if ud:
            return (create_schema(UserDefsSchema, False)).jsonify(ud)
        return {'message': USERDEFS_NOT_FOUND}, 404


class UserDefsByVerificationResource(Resource):
    def get(self, id):
        userdefs_id = (a.get_element_by_id(Verification, id)).userdefs.id
        return UserDefsByIdResource.get(self, userdefs_id)


class UserPropsListResource(Resource):
    def get(self):
        up = a.get_all_elements(UserProps)
        return (create_schema(UserPropsSchema, True)).jsonify(up)


class UserPropsByIdResource(Resource):
    def get(self, id):
        up = a.get_element_by_id(UserProps, id)
        return (create_schema(UserPropsSchema, False)).jsonify(up)


class UserPropsByVerificationResource(Resource):
    def get(self, id):
        userprops_id = (a.get_element_by_id(Verification, id)).userprops.id
        return UserPropsByIdResource.get(self, userprops_id)


class ConstraintsListResource(Resource):
    def get(self):
        c = a.get_all_elements(Constraints)
        return (create_schema(ConstraintsSchema, True)).jsonify(c)


class ConstraintsByIdResource(Resource):
    def get(self, id):
        c = a.get_element_by_id(Constraints, id)
        return (create_schema(ConstraintsSchema, False)).jsonify(c)


class ConstraintsByVerificationResource(Resource):
    def get(self, id):
        constraints_id = (a.get_element_by_id(Verification, id)).constraints.id
        return ConstraintsByIdResource.get(self, constraints_id)


class VerificationListResource(Resource):
    def get(self):
        v = a.get_all_elements(Verification)
        return (create_schema(VerificationSchema, True)).jsonify(v)

    def post(self):
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


class VerificationByIdResource(Resource):
    def get(self, id):
        v = a.get_element_by_id(Verification, id)
        return (create_schema(VerificationSchema, False)).jsonify(v)

    def delete(self, id):
        v = Verification.query.get(id)
        db.session.delete(v)
        db.session.commit()
        return "Verification was successfully deleted"


class VerificationByResult(Resource):
    def get(self, id):
        verification = (a.get_element_by_id(Result, id)).verification
        return (create_schema(VerificationSchema, False)).jsonify(verification)


class LatestVerificationResource(Resource):
    def get(self):
        v = a.get_latest_verification()
        return (create_schema(VerificationSchema, False)).jsonify(v)


class ResultListResource(Resource):
    def get(self):
        r = a.get_all_elements(Result)
        return (create_schema(ResultSchema, True)).jsonify(r)


class ResultByIdResource(Resource):
    def get(self, id):
        r = a.get_element_by_id(Result, id)
        return (create_schema(ResultSchema, False)).jsonify(r)


class ResultByVerificationResource(Resource):
    def get(self, id):
        verification = a.get_element_by_id(Verification, id)
        return (create_schema(ResultSchema, True)).jsonify(verification.results)


class CounterExampleListResource(Resource):
    def get(self):
        ce = a.get_all_elements(CounterExample)
        return (create_schema(CounterExampleSchema, True)).jsonify(ce)


class CounterExampleByIdResource(Resource):
    def get(self, id):
        ce = a.get_element_by_id(CounterExample, id)
        return (create_schema(CounterExampleSchema, False)).jsonify(ce)


class CounterExampleResourceByResult(Resource):
    def get(self, id):
        counter_example = (a.get_element_by_id(Result, id)).counter_example
        if counter_example:
            return (create_schema(CounterExampleSchema, False)).jsonify(counter_example)
        else:
            return "Record not found", 400
