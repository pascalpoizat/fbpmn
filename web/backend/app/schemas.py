from app import ma
from app.models import Status, Constraints, CounterExample, Model, UserDefs, UserProps, Verification, Result
from app.context import Communication, Property
from marshmallow_enum import EnumField

VERIFICATION_BY_ID = "api.verifications_verification_by_id"


class ModelSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Model
        include_relationships = True
        load_instance = True
    verification = ma.HyperlinkRelated(VERIFICATION_BY_ID)


class UserDefsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = UserDefs
        include_relationships = True
    verification = ma.HyperlinkRelated(VERIFICATION_BY_ID)


class UserPropsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = UserProps
        include_relationships = True
    verification = ma.HyperlinkRelated(VERIFICATION_BY_ID)


class ConstraintsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Constraints
        include_relationships = True
    verification = ma.HyperlinkRelated(VERIFICATION_BY_ID)


class VerificationSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Verification
        include_relationships = True

    status = EnumField(Status)
    pub_date = ma.DateTime(format='%Y-%m-%dT%H:%M')
    results = ma.List(ma.HyperlinkRelated("api.results_result_by_id"))
    model = ma.HyperlinkRelated("api.models_model_by_id")
    userdefs = ma.HyperlinkRelated("api.userdefs_user_defs_by_id")
    userprops = ma.HyperlinkRelated("api.userprops_user_props_by_id")
    constraints = ma.HyperlinkRelated("api.constraints_constraints_by_id")


class ResultSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Result
        include_relationships = True

    communication = EnumField(Communication)
    property = EnumField(Property)
    verification = ma.HyperlinkRelated(VERIFICATION_BY_ID)


class CounterExampleSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = CounterExample
        include_realtionships = True
    result = ma.HyperlinkRelated("api.results_result_by_id")
