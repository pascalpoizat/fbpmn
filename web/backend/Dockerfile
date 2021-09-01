FROM python:latest
WORKDIR /api

ENV VERSION="0.3.7"

RUN mkdir bin && \
    cd bin && \
    wget -q https://github.com/pascalpoizat/fbpmn/releases/download/v${VERSION}/fbpmn-${VERSION}-linux.x86_64.zip &&\
    unzip fbpmn-${VERSION}-linux.x86_64.zip && \
    cd .. && \
    wget https://github.com/pascalpoizat/fbpmn/archive/refs/tags/v${VERSION}.zip && \
    unzip v${VERSION}.zip && \
    wget https://github.com/tlaplus/tlaplus/releases/download/v1.6.0/tla2tools.jar
RUN apt-get update && \
    apt-get install -y wget apt-transport-https software-properties-common && \
    wget -q https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    apt-get update && \
    apt-get install -y powershell
RUN apt-get update && apt-get install -y openjdk-11-jdk
COPY requirements.txt config.py .flaskenv ./
COPY wfbpmn-check /api/bin
# until the next release with wfbpmn-check on fbpmn public repo
COPY ./app app/
COPY ./data data/
RUN pip install -r ./requirements.txt
ENV FBPMN_HOME=/api/fbpmn-${VERSION} TLA2TOOLS_HOME=/api
ENV PATH="$FBPMN_HOME/scripts:/api/bin:$PATH"

EXPOSE 5000
CMD ["gunicorn", "-b", "0.0.0.0:5000", "app.routes:app", "--timeout", "120", "-w", "1", "--threads", "12"]
