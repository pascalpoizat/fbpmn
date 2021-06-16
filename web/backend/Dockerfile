FROM python:3.9
WORKDIR /app

COPY requirements.txt app.py .flaskenv ./
RUN pip install -r ./requirements.txt
ENV FLASK_ENV production

EXPOSE 5000
CMD ["gunicorn", "-b", "127.0.0.1:5000", "app:app"]