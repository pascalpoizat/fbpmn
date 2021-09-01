from app import ma
from app.models import Communication, Status, CounterExample, Model, Value, Verification, Result
from marshmallow_enum import EnumField

VERIFICATION_BY_ID = "api.verifications_verification_by_id"


class ModelSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Model
        include_relationships = True
        load_instance = True
    verification = ma.HyperlinkRelated(VERIFICATION_BY_ID)


class VerificationSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Verification
        include_fk = True
    status = EnumField(Status)
    value = EnumField(Value)
    pub_date = ma.DateTime(format='%d/%m\n%H:%M')
    results = ma.List(ma.HyperlinkRelated("api.results_result_by_id"))
    model = ma.HyperlinkRelated("api.models_model_by_id")


class ResultSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Result
        include_relationships = True

    communication = EnumField(Communication)
    verification = ma.HyperlinkRelated(VERIFICATION_BY_ID)


class CounterExampleSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = CounterExample
        include_realtionships = True
    result = ma.HyperlinkRelated("api.results_result_by_id")
