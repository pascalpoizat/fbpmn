FROM python:3.9
WORKDIR /api

COPY requirements.txt install config.py .flaskenv ./
COPY install bin/
COPY ./app app/
RUN pip install -r ./requirements.txt
RUN chmod +x bin/install
RUN ./bin/install

ENV FLASK_ENV=production FBPMN_HOME=/api/fbpmn TLA2TOOLS_HOME=/api
ENV PATH="$FBPMN_HOME/scripts:/api/bin:$PATH"
ENV DB_HOST='' DB_NAME='' DB_USER='' DB_PASSWORD=''

EXPOSE 5000
CMD ["gunicorn", "-b", ":5000", "app.routes:app"]