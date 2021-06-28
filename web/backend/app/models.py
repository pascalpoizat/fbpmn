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
        version = subprocess.check_output(
            "fbpmn version", shell=True, universal_newlines=True)
        version = version.split('.')
        self.major = int(version[0])
        self.minor = int(version[1])
        self.patch = version[2].splitlines()


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

    def set_status(self):
        # TODO conditions si fail
        self.status = Status.DONE.name

    # TODO verifier all_ok()
    def all_ok(self):
        for r in self.results:
            if r.is_ok() == False:
                return False
        return True


class Result(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    communication = db.Column(db.Enum(Communication))
    property = db.Column(db.Enum(Property))
    value = db.Column(db.Boolean)
    verification_id = db.Column(db.Integer, db.ForeignKey('verification.id'))

    def __init__(self, comm, prop, verif):  # verif = verif1.id
        self.communication = comm
        self.property = prop
        self.verification_id = verif

    def get_id(self):
        return self.id

    def get_context(self):
        return self.communication + self.property  # TODO list plutôt

    def set_value(self, file):
        # TODO à partir du JSON initialisé la bonne valeur pour le bon contexte
        self.value = value

    def is_ok(self):
        if self.value == True:
            return True
        else:
            return False


class Application():
    def create_verification():

        # 1. créer une instance de vérification
        # 2. lancer la vérification avec fbpmn-check sur le modèle
        # 3. récupérer le workdir de fbpmn-check -> get_workir
        # 4. créer des instances de résults pour chaque config, les initialiser avec le json produit
        '''
        v1 = Verification(m1.id)
        db.session.add(v1)
        db.session.commit()

        for comm in Communication:
            for prop in Property:
                r1 = Result(comm.name, prop.name, True, v1.id)
                db.session.add(r1)
                db.session.commit()
        '''
        pass

# TODO def is_ok_verif():

# TODO def is_ok_result():


def get_workir_with_output(output):
    # TODO récupérer le workdir de fbpmn-check à partir de l'output de la commande
    # TODO peut être trouver une meilleure solution
    pass
