SQLAlchemy' migrations:

The structure of the database being to change, we work with the Flask-Migrate package.

Firstly, in the current directory of the Flask application, run:

```sh
flask db init
```

Then, at each modification in the models.py classes, run:

```sh
flask db migrate
flask db upgrade
```
