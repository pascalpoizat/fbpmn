FROM python:3.9
WORKDIR /api

COPY requirements.txt config.py .flaskenv ./
RUN pip install -r ./requirements.txt
COPY ./app app/
ENV FLASK_ENV production

EXPOSE 5000
CMD ["gunicorn", "-b", "0.0.0.0:5000", "app.routes:app"]