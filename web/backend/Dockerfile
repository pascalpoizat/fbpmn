FROM python:3.9
WORKDIR /api

COPY requirements.txt config.py .flaskenv ./
COPY ./app app/
RUN pip install -r ./requirements.txt
RUN mkdir bin && \
    cd bin && \
    wget -q https://github.com/pascalpoizat/fbpmn/releases/download/v0.3.7/fbpmn-0.3.7-linux.x86_64.zip &&\
    unzip fbpmn-0.3.7-linux.x86_64.zip && \
    cd .. && \
    wget https://github.com/pascalpoizat/fbpmn/archive/refs/tags/v0.3.7.zip && \
    unzip v0.3.7.zip && \
    wget https://github.com/tlaplus/tlaplus/releases/download/v1.6.0/tla2tools.jar

ENV FLASK_ENV=production FBPMN_HOME=/api/fbpmn-0.3.7 TLA2TOOLS_HOME=/api
ENV PATH="$FBPMN_HOME/scripts:/api/bin:$PATH"
ENV DB_HOST='' DB_NAME='' DB_USER='' DB_PASSWORD=''
RUN apt-get update && \
    apt-get install -y wget apt-transport-https software-properties-common && \
    wget -q https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    apt-get update && \
    apt-get install -y powershell

EXPOSE 5000
CMD ["gunicorn", "-b", ":5000", "app.routes:app"]