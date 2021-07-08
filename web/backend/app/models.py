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
    FAILED = auto()


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
        'Verification', backref='model', lazy='dynamic')

    def __init__(self, content_file):
        self.content = content_file
        self.name = (ElemTree.fromstring(content_file).find(
            '{http://www.omg.org/spec/BPMN/20100524/MODEL}collaboration')).get('id')


class Verification(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    status = db.Column(db.Enum(Status))
    pub_date = db.Column(db.DateTime, index=True,
                         default=datetime.utcnow)
    output = db.Column(db.Text(10000))
    model_id = db.Column(db.Integer, db.ForeignKey('model.id'))
    results = db.relationship('Result', backref='verification', lazy='dynamic')

    def __init__(self):
        self.status = Status.PENDING.name  # TODO doit afficher juste PENDING

    def set_output(self, output):
        self.output = output

    def set_model(self, model_id):
        self.model_id = model_id

    def get_id(self):
        return self.id

    def get_model(self):
        return self.model_id

    def change_status(self):
        if self.all_ok():
            self.status = Status.DONE.name
        else:
            self.status = Status.FAILED.name

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

    def launch_check(self, model_name):
        output = subprocess.getoutput(
            f'fbpmn-check /tmp/{model_name}.bpmn')
        self.set_output(output)
        return output

    def results_list(self, workdir, model_name):
        f = open(f'/tmp/{workdir}/{model_name}.json')
        data = json.load(f)
        f.close()
        results = []
        for comm in Communication:
            for prop in Property:
                results.append(Result(comm.name, prop.name, self.id))
                value = data[f'{model_name}'][f'{comm.name}'][f'{prop.name}']['value']
                results[len(results)-1].set_value(value)
                db.session.add(results[len(results)-1])
        self.change_status()
        db.session.commit()
        return self.results.all()


class Result(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    communication = db.Column(db.Enum(Communication))
    property = db.Column(db.Enum(Property))
    value = db.Column(db.Boolean)
    verification_id = db.Column(db.Integer, db.ForeignKey('verification.id'))
    # autre nom -> models n'est pas BD
    # print('verification.id')  # -> doit marcher

    def __init__(self, comm, prop, verif):
        self.communication = comm
        self.property = prop
        self.verification_id = verif

    def get_id(self):
        return self.id

    def get_context(self):
        return self.communication + self.property  # TODO classe à part entière?

    def get_verification(self):
        return self.verification_id

    def set_value(self, value):
        self.value = value

    def is_ok(self):
        if self.value:
            return True
        else:
            return False


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

    def get_model_by_id(self, model_id):
        return Model.query.get(model_id)

    def get_verification_by_id(self, verification_id):
        return Verification.query.get(verification_id)

    def get_latest_verification(self):
        verifications = Verification.query.filter_by().order_by(
            db.desc(Verification.pub_date)).all()
        return verifications[0]

    def get_result_by_id(self, result_id):
        return Result.query.get(result_id)

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
