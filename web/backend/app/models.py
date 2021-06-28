import re
import json
from app import db
from datetime import datetime
from app.context import Communication, Property
from enum import Enum, auto
import xml.etree.ElementTree as ET
import subprocess


class Status(Enum):
    PENDIND = auto()
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
        'Verification', backref='verification', lazy='dynamic')

    def __init__(self, content_file):
        self.content = content_file
        self.name = (ET.fromstring(content_file).find(
            '{http://www.omg.org/spec/BPMN/20100524/MODEL}collaboration')).get('id')


class Verification(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    status = db.Column(db.Enum(Status))
    pub_date = db.Column(db.DateTime, index=True,
                         default=datetime.utcnow)
    model_id = db.Column(db.Integer, db.ForeignKey('model.id'))
    results = db.relationship('Result', backref='results', lazy='dynamic')

    def __init__(self, model):
        self.status = Status.PENDIND.name  # TODO corriger -> doit afficher juste PENDING
        self.model_id = model

    def get_id(self):
        return self.id

    def get_model(self):
        return self.model_id

    def get_status(self):
        return self.status

    def change_status(self):
        # TODO conditions si fail
        self.status = Status.DONE.name

    # TODO verifier all_ok()
    def all_ok(self):
        v = Verification.query.get(self.id)
        for r in v.results.all():
            if not r.is_ok():
                return False
        return True


class Result(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    communication = db.Column(db.Enum(Communication))
    property = db.Column(db.Enum(Property))
    value = db.Column(db.Boolean)
    verification_id = db.Column(db.Integer, db.ForeignKey('verification.id'))

    def __init__(self, comm, prop, verif):
        self.communication = comm
        self.property = prop
        self.verification_id = verif

    def get_id(self):
        return self.id

    def get_context(self):
        return self.communication + self.property  # TODO list plutôt

    def set_value(self, value):
        self.value = value

    def is_ok(self):
        if self.value == True:
            return True
        else:
            return False


def get_workdir(output):
    # TODO peut-être trouver une meilleure solution
    firstline = output.split('\n', 1)[0]
    workdir = (re.search(r'/tmp/(.+) with', firstline)).group(1)
    return workdir


class Application():
    def create_verification(self, model):
        # 1. créer une instance de vérification
        v1 = Verification(model.id)
        db.session.add(v1)
        db.session.commit()
        # 2. lancer la vérification avec fbpmn-check sur le modèle
        output = subprocess.getoutput(f'fbpmn-check /tmp/{model.name}.bpmn')
        # 3. récupérer le workdir de fbpmn-check -> get_workir
        workdir = get_workdir(output)
        # 4. charger le json stocké à /tmp/workdir/{model.name}.json
        f = open(f'/tmp/{workdir}/{model.name}.json')
        data = json.load(f)
        f.close()
        # 5. créer des instances de résults pour chaque config, les initialiser avec le json produit
        for comm in Communication:
            for prop in Property:
                r1 = Result(comm.name, prop.name, v1.id)
                value = data[f'{model.name}'][f'{comm.name}'][f'{prop.name}']['value']
                r1.set_value(value)
                db.session.add(r1)
                del r1
        v1.change_status()
        db.session.commit()
        return v1

    def create_bpmn_file(self, content_request):
        m1 = Model(content_request)
        db.session.add(m1)
        db.session.commit()
        open(f'/tmp/{m1.name}.bpmn', 'x')
        f = open(f'/tmp/{m1.name}.bpmn', 'w')
        f.write(f'{m1.content}')
        f.close
        return m1

    # TODO def is_ok_verif():
    #     verifications = Verification.query.all()

    # TODO def is_ok_result():
