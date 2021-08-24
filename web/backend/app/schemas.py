from app import ma
from app.models import Status, Value, Constraints, CounterExample, Model, UserDefs, UserProps, Verification, Result
from app.context import Communication, Property
from marshmallow_enum import EnumField


class ModelSchema(ma.SQLAlchemySchema):
    class Meta:
        model = Model
    id = ma.auto_field()
    name = ma.auto_field()
    content = ma.auto_field()
    verification = ma.auto_field()


class UserDefsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = UserDefs
    verification = ma.HyperlinkRelated("verifications")


class UserPropsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = UserProps
    verification = ma.HyperlinkRelated("verifications")


class ConstraintsSchema(ma.SQLAlchemyAutoSchema):
    class Meta:
        model = Constraints


class VerificationSchema(ModelSchema):
    status = EnumField(Status)
    model_id = ma.HyperlinkRelated("models")

    class Meta:
        model = Verification
        include_fk = True


class ResultSchema(ma.SQLAlchemySchema):
    id = ma.auto_field()
    communication = EnumField(Communication)
    property = EnumField(Property)
    value = ma.auto_field()
    counter_example = ma.HyperlinkRelated("counter_examples")

    class Meta:
        model = Result


class CounterExampleSchema(ma.SQLAlchemySchema):
    class Meta:
        model = CounterExample
    id = ma.auto_field()
    lcex = ma.auto_field()
    lstatus = ma.auto_field()
    lname = ma.auto_field()
    lmodel = ma.auto_field()
    result_id = ma.HyperlinkRelated("results")
