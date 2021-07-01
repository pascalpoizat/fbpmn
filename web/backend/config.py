import os


class Config(object):
    SQLALCHEMY_DATABASE_URI = 'mysql://{}:{}@{}/{}'.format(
        os.getenv('DB_USER', 'admin'),
        os.getenv('DB_PASSWORD', ''),
        os.getenv('DB_HOST', 'mysql'),
        os.getenv('DB_NAME', 'fBPMN_db')
    )
    SQLALCHEMY_TRACK_MODIFICATIONS = False
    CORS_HEADERS = 'Content-Type'
