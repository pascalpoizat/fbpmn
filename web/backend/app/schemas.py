from app import ma
from app.models import Status, Value, Constraints, CounterExample, Model, UserDefs, UserProps, Verification, Result
from app.context import Communication, Property
from marshmallow_enum import EnumField


class ModelSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Model
        include_relationships = True
        load_instance = True
    verification = ma.HyperlinkRelated("get_verification_by_id")


class UserDefsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = UserDefs
        include_relationships = True
    verification = ma.HyperlinkRelated("get_verification_by_id")


class UserPropsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = UserProps
        include_relationships = True
    verification = ma.HyperlinkRelated("get_verification_by_id")


class ConstraintsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Constraints
        include_relationships = True
    verification = ma.HyperlinkRelated("get_verification_by_id")


class VerificationSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Verification
        include_relationships = True

    status = EnumField(Status)
    pub_date = ma.DateTime(format='%Y-%m-%dT%H:%M')
    results = ma.List(ma.HyperlinkRelated("get_result_by_id"))
    model = ma.HyperlinkRelated("get_model_by_id")
    userdefs = ma.HyperlinkRelated("get_userdefs_by_id")
    userprops = ma.HyperlinkRelated("get_userprops_by_id")
    constraints = ma.HyperlinkRelated("get_constraints_by_id")


class ResultSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Result
        include_relationships = True

    communication = EnumField(Communication)
    property = EnumField(Property)
    verification = ma.HyperlinkRelated("get_verification_by_id")
    counter_example = ma.HyperlinkRelated("get_counter_examples_by_id")


class CounterExampleSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = CounterExample
        include_realtionships = True
    result = ma.HyperlinkRelated("get_result_by_id")
