from flask import request
from flask_restplus import Resource, fields, Namespace

from app.models import Application, Model, Verification
from app.schemas import ModelSchema, VerificationSchema

MODEL_NOT_FOUND = "Model not found."
VERIFICATION_NOT_FOUND = "Verification not found."


a = Application()

models_ns = Namespace('models', description='models related operations')
verifications_ns = Namespace(
    'verifications', description='verifications related operations')

model_schema = ModelSchema()
model_list_schema = ModelSchema(many=True)

verification_schema = VerificationSchema()
verification_list_schema = VerificationSchema(many=True)


model = models_ns.model('Model', {
    'content': fields.String('Content of the model'),
    'id': fields.Integer,
    'name': fields.String('Name of the model'),
    'verification': fields.String('URL to the verification')
})


class ModelResource(Resource):
    def get(self, id):
        model_data = a.get_element_by_id(Model, id)
        if model_data:
            return model_schema.dump(model_data)
        return {'message': MODEL_NOT_FOUND}, 404


class VerificationResource(Resource):
    def get(self, id):
        verification_data = a.get_element_by_id(Verification, id)
        if verification_data:
            return verification_schema.dump(verification_data)
        return {'message': MODEL_NOT_FOUND}, 404
