import re
import json
from app import db
from datetime import datetime
from app.context import Communication, Property
from enum import Enum, auto
import xml.etree.ElementTree as ElemTree
import subprocess


def get_workdir(output):
    # TODO peut-être trouver une meilleure solution que re.search
    firstline = output.split('\n', 1)[0]
    workdir = (re.search(r'/tmp/(.+) with', firstline)).group(1)
    return workdir


class Status(Enum):
    PENDING = auto()
    DONE = auto()
    ABORTED = auto()


class Value(Enum):
    FAIL = auto()
    SUCCESS = auto()
    INCONCLUSIVE = auto()


class Version:
    def __init__(self):
        version = (subprocess.getoutput("fbpmn version")).split('.')
        self.major = int(version[0])
        self.minor = int(version[1])
        self.patch = int(version[2])


class Model(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    name = db.Column(db.String(80), nullable=False)
    content = db.Column(db.Text(10000), nullable=False)
    verification = db.relationship(
        'Verification', cascade="all,delete", backref='model', lazy='dynamic')

    def __init__(self, content_file):
        self.content = content_file
        self.name = (ElemTree.fromstring(content_file).find(
            '{http://www.omg.org/spec/BPMN/20100524/MODEL}collaboration')).get('id')


class UserDefs(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    content = db.Column(db.Text(10000), nullable=False)
    verification = db.relationship(
        'Verification', cascade="all,delete", backref='userdefs', lazy='dynamic')

    def __init__(self, content_file):
        self.content = content_file


class UserProps(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    content = db.Column(db.Text(10000), nullable=False)
    verification = db.relationship(
        'Verification', cascade="all,delete", backref='userprops', lazy='dynamic')

    def __init__(self, content_file):
        self.content = content_file


class Constraints(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    content = db.Column(db.Text(10000), nullable=False)
    verification = db.relationship(
        'Verification', cascade="all,delete", backref='constraints', lazy='dynamic')

    def __init__(self, content_file):
        self.content = content_file


class Verification(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    status = db.Column(db.Enum(Status))
    pub_date = db.Column(db.DateTime, index=True,
                         default=datetime.utcnow)
    duration = db.Column(db.Integer)
    output = db.Column(db.Text(10000))
    model_id = db.Column(db.Integer, db.ForeignKey('model.id'))
    userdefs_id = db.Column(db.Integer, db.ForeignKey('user_defs.id'))
    userprops_id = db.Column(db.Integer, db.ForeignKey('user_props.id'))
    constraints_id = db.Column(db.Integer, db.ForeignKey('constraints.id'))
    results = db.relationship(
        'Result', cascade="all,delete", backref='verification', lazy='dynamic')

    def __init__(self):
        self.status = Status.PENDING.name

    def set_output(self, output):
        self.output = output

    def set_model(self, model_id):
        self.model_id = model_id

    def set_duration(self, duration):
        self.duration = duration

    def get_id(self):
        return self.id

    def get_model(self):
        return self.model.first()

    def get_value(self):
        if self.status == Status.DONE.name:
            if self.all_ok():
                return Value.SUCCESS.name
            else:
                return Value.FAIL.name
        else:
            return Value.INCONCLUSIVE.name

    def aborted(self):
        self.status = Status.ABORTED.name
        db.session.commit()

    def all_ok(self):
        v = Verification.query.get(self.id)
        for r in v.results.all():
            if not r.is_ok():
                return False
        return True

    def create_model(self, content_request):
        m = Model(content_request)
        db.session.add(m)
        db.session.commit()
        self.set_model(m.id)
        f = open(f'/tmp/{m.name}.bpmn', 'w')
        f.write(f'{m.content}')
        f.close()
        return m

    def create_userdefs(self, content_request, model_name):
        ud = UserDefs(content_request)
        db.session.add(ud)
        db.session.commit()
        f = open(f'/tmp/{model_name}.userdefs', 'w')
        f.write(f'{ud.content}')
        f.close()

    def create_userprops(self, content_request, model_name):
        up = UserProps(content_request)
        db.session.add(up)
        db.session.commit()
        f = open(f'/tmp/{model_name}.userdefs', 'w')
        f.write(f'{up.content}')
        f.close()

    def create_constraints(self, content_request, model_name):
        pass

    def launch_check(self, model_name):
        begin = datetime.now()
        output = subprocess.getoutput(
            f'wfbpmn-check /tmp/{model_name}.bpmn')
        self.set_output(output)
        end = datetime.now()
        self.set_duration((end - begin).seconds)
        return output

    def create_results_list(self, workdir, model_name):
        f = open(f'/tmp/{workdir}/{model_name}.json')
        data = json.load(f)
        f.close()
        results = []
        for comm in Communication:
            for prop in Property:
                results.append(Result(comm.name, prop.name, self.id))
                value = data[f'{model_name}'][f'{comm.name}'][f'{prop.name}']['value']
                results[len(results)-1].set_value(value)
        db.session.add_all(results)
        self.status = Status.DONE.name
        db.session.commit()
        return self.results.all()

    def create_counter_examples(self, workdir, model_name, results_list):
        subprocess.run(
            f'cd /tmp/{workdir} ; fbpmn-log-transform json ; cd', shell=True)
        counter_examples = []
        for result in results_list:
            if not result.value:
                counter_examples.append(
                    result.create_counter_example(workdir, model_name))
        db.session.add_all(counter_examples)
        db.session.commit()


class Result(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    communication = db.Column(db.Enum(Communication))
    property = db.Column(db.Enum(Property))
    value = db.Column(db.Boolean)
    counter_example = db.relationship(
        'CounterExample', cascade="all,delete", backref='result', lazy='dynamic')
    verification_id = db.Column(db.Integer, db.ForeignKey('verification.id'))

    def __init__(self, comm, prop, verif):
        self.communication = comm
        self.property = prop
        self.verification_id = verif

    def get_id(self):
        return self.id

    def get_context(self):
        return self.communication.name + self.property.name

    def get_verification(self):
        return self.verification

    def get_counter_example(self):
        return self.counter_example.first()

    def set_value(self, value):
        self.value = value

    def create_counter_example(self, workdir, model_name):
        f = open(
            f'/tmp/{workdir}/{model_name}.{self.communication.name}.{self.property.name}.json')
        data = json.load(f)
        f.close()
        return CounterExample(json.dumps(data["lcex"]), str(data["lstatus"]), str(data["lname"]), str(data["lmodel"]), self.id)

    def is_ok(self):
        if self.value:
            return True
        else:
            return False


class CounterExample(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    lcex = db.Column(db.Text(100000))
    lstatus = db.Column(db.Text(100))
    lname = db.Column(db.Text(100))
    lmodel = db.Column(db.Text(100))
    result_id = db.Column(db.Integer, db.ForeignKey('result.id'))

    def __init__(self, lcex, lstatus, lname, lmodel, result):
        self.lcex = lcex
        self.lstatus = lstatus
        self.lname = lname
        self.lmodel = lmodel
        self.result_id = result

    def get_result(self):
        return self.result


class Application:
    def create_verification(self):
        v = Verification()
        db.session.add(v)
        db.session.commit()
        return v

    def get_all_models(self):
        return Model.query.all()

    def get_all_verifications(self):
        return Verification.query.all()

    def get_all_results(self):
        return Result.query.all()

    def get_all_counter_examples(self):
        return CounterExample.query.all()

    def get_model_by_id(self, model_id):
        return Model.query.get(model_id)

    def get_verification_by_id(self, verification_id):
        return Verification.query.get(verification_id)

    def get_latest_verification(self):
        verifications = Verification.query.filter_by().order_by(
            db.desc(Verification.id)).all()
        return verifications[0]

    def get_result_by_id(self, result_id):
        return Result.query.get(result_id)

    def get_counter_example_by_id(self, counter_example_id):
        return CounterExample.query.get(counter_example_id)

    def is_ok_verif(self, verification_id):
        v = Application.get_verification_by_id(verification_id)
        if v.all_ok():
            return True
        else:
            return False

    def is_ok_result(self, result_id):
        r = Application.get_result_by_id(result_id)
        if r.is_ok():
            return True
        else:
            return False
