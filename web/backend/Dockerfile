FROM python:latest
WORKDIR /api

RUN mkdir bin && \
    cd bin && \
    wget -q https://github.com/pascalpoizat/fbpmn/releases/download/v0.3.7/fbpmn-0.3.7-linux.x86_64.zip &&\
    unzip fbpmn-0.3.7-linux.x86_64.zip && \
    cd .. && \
    wget https://github.com/pascalpoizat/fbpmn/archive/refs/tags/v0.3.7.zip && \
    unzip v0.3.7.zip && \
    wget https://github.com/tlaplus/tlaplus/releases/download/v1.6.0/tla2tools.jar
RUN apt-get update && \
    apt-get install -y wget apt-transport-https software-properties-common && \
    wget -q https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    apt-get update && \
    apt-get install -y powershell
COPY requirements.txt config.py .flaskenv ./
COPY ./app app/
COPY ./data data/
RUN pip install -r ./requirements.txt
ENV FBPMN_HOME=/api/fbpmn-0.3.7 TLA2TOOLS_HOME=/api
ENV PATH="$FBPMN_HOME/scripts:/api/bin:$PATH"


EXPOSE 5000
CMD ["gunicorn", "-b", "0.0.0.0:5000", "app.routes:app"]
