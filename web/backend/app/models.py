import re
import json
from app import db
from datetime import datetime
from enum import Enum, auto
import xml.etree.ElementTree as ElemTree
import subprocess

CASCADE = "all,delete"


def get_workdir(output):
    return (re.search(r'/tmp/(.+) with', output)).group(1)


class Communication(Enum):
    Network01Bag = auto()
    Network02FifoPair = auto()
    Network03Causal = auto()
    Network04Inbox = auto()
    Network05Outbox = auto()
    Network06Fifo = auto()
    Network07RSC = auto()


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
        'Verification', cascade=CASCADE, backref='model', uselist=False)

    def __init__(self, content_file):
        self.content = content_file
        self.name = (ElemTree.fromstring(content_file).find(
            '{http://www.omg.org/spec/BPMN/20100524/MODEL}collaboration')).get('id')


class UserNets(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    content = db.Column(db.Text(10000), nullable=False)
    verification = db.relationship(
        'Verification', cascade=CASCADE, backref='usernets', uselist=False)

    def __init__(self, content_file):
        content = ""
        for usernet in content_file:
            content += str(usernet + "\n")
        self.content = content


class UserDefs(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    content = db.Column(db.Text(10000), nullable=False)
    verification = db.relationship(
        'Verification', cascade=CASCADE, backref='userdefs', uselist=False)

    def __init__(self, content_file):
        content = ""
        for userdef in content_file:
            content += str(userdef + "\n")
        self.content = content


class UserProps(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    content = db.Column(db.Text(10000), nullable=False)
    verification = db.relationship(
        'Verification', cascade=CASCADE, backref='userprops', uselist=False)

    def __init__(self, content_file):
        content = ""
        for userprop in content_file:
            content += str(userprop + "\n")
        self.content = content


class Constraints(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    content = db.Column(db.Text(10000), nullable=False)
    verification = db.relationship(
        'Verification', cascade=CASCADE, backref='constraints', uselist=False)

    def __init__(self, content_file):
        self.content = content_file


class Verification(db.Model):
    id = db.Column(db.Integer, primary_key=True, autoincrement=True)
    status = db.Column(db.Enum(Status))
    value = db.Column(db.Enum(Value))
    pub_date = db.Column(db.DateTime, index=True,
                         default=datetime.utcnow)
    duration = db.Column(db.Integer)
    output = db.Column(db.Text(10000))
    model_id = db.Column(db.Integer, db.ForeignKey('model.id'))
    userdefs_content = db.Column(
        db.Text(10000), db.ForeignKey('user_defs.content'))
    usernets_content = db.Column(
        db.Text(10000), db.ForeignKey('user_nets.content'))
    userprops_content = db.Column(
        db.Text(10000), db.ForeignKey('user_props.content'))
    constraints_content = db.Column(
        db.Text(10000), db.ForeignKey('constraints.content'))
    results = db.relationship(
        'Result', cascade=CASCADE, backref='verification', lazy="dynamic")

    def __init__(self):
        self.status = Status.PENDING.name

    def set_output(self, output):
        self.output = output

    def set_model(self, model_id):
        self.model_id = model_id

    def set_usernets_content(self, usernets):
        self.usernets_content = usernets

    def set_userdefs_content(self, userdefs):
        self.userdefs_content = userdefs

    def set_userprops_content(self, userprops):
        self.userprops_content = userprops

    def set_constraints_content(self, constraints):
        self.constraints_content = constraints

    def set_duration(self, duration):
        self.duration = duration

    def set_value(self):
        if self.status == Status.DONE.name:
            if self.all_ok():
                self.value = Value.SUCCESS.name
            else:
                self.value = Value.FAIL.name
        else:
            self.value = Value.INCONCLUSIVE.name

    def get_id(self):
        return self.id

    def get_model(self):
        return self.model.first()

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

    def create_file(self, type, content_request, model_name):
        element = type(content_request)
        db.session.add(element)
        db.session.commit()
        if type == UserNets:
            self.set_usernets_content(element.content)
            f = open(f'/tmp/{model_name}.usernets', 'w')
        if type == UserProps:
            self.set_userprops_content(element.content)
            f = open(f'/tmp/{model_name}.userprops', 'w')
        if type == Constraints:
            self.set_constraints_content(element.content)
            f = open(f'/tmp/{model_name}.constraint', 'w')
        f.write(f'{element.content}')
        f.close()

    def create_properties_files(self, def_content, prop_content, model_name):
        userdefs = UserDefs(def_content)
        userprops = UserProps(prop_content)
        db.session.add(userdefs)
        db.session.add(userprops)
        db.session.commit()
        self.set_userdefs_content(userdefs.content)
        f = open(f'/tmp/{model_name}.userdefs', 'w')
        f.write(f'---------------- MODULE UserProperties ----------------\n\n'
                'VARIABLES nodemarks, edgemarks, net\n\n'
                f'{userdefs.content}'
                '\n================================================================')
        self.set_userprops_content(userprops.content)
        f = open(f'/tmp/{model_name}.userprops', 'w')
        f.write(f'{userprops.content}')
        f.close()

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
        for (k, v) in data[f'{model_name}'].items():
            for (key, value) in data[f'{model_name}'][f'{k}'].items():
                results.append(Result(k, key, self.id))
                value = value['value']
                results[len(results)-1].set_value(value)
        db.session.add_all(results)
        self.status = Status.DONE.name
        self.set_value()
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
    property = db.Column(db.Text(100))
    value = db.Column(db.Boolean)
    counter_example = db.relationship(
        'CounterExample', cascade=CASCADE, backref='result', uselist=False)
    verification_id = db.Column(db.Integer, db.ForeignKey('verification.id'))

    def __init__(self, comm, property, verif):
        self.communication = comm
        self.property = property
        self.verification_id = verif

    def get_id(self):
        return self.id

    def get_context(self):
        return self.communication.name

    def get_verification(self):
        return self.verification

    def get_counter_example(self):
        return self.counter_example.first()

    def set_value(self, value):
        self.value = value

    def create_counter_example(self, workdir, model_name):
        f = open(
            f'/tmp/{workdir}/{model_name}.{self.communication.name}.{self.property}.json')
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

    def get_all_elements(self, type):
        return type.query.all()

    def get_element_by_id(self, type, id):
        return type.query.get(id)

    def get_latest_verification(self):
        verifications = Verification.query.filter_by().order_by(
            db.desc(Verification.id)).all()
        return verifications[0]

    def is_ok_verif(self, verification_id):
        v = Application.get_element_by_id(Verification, verification_id)
        if v.all_ok():
            return True
        else:
            return False

    def is_ok_result(self, result_id):
        r = Application.get_element_by_id(Result, result_id)
        if r.is_ok():
            return True
        else:
            return False
