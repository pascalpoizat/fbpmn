import os


class Config(object):
    SQLALCHEMY_DATABASE_URI = 'mysql://{}:{}@{}/{}'.format(
        os.getenv('DB_USER'),
        os.getenv('DB_PASSWORD'),
        os.getenv('DB_HOST'),
        os.getenv('DB_NAME')
    )
    SQLALCHEMY_TRACK_MODIFICATIONS = False
    CORS_HEADERS = 'Content-Type'
