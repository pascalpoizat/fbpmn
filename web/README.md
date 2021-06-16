Template of React + Flask application (not for production, soon to be Dockerized)

References:

- https://blog.miguelgrinberg.com/post/how-to-create-a-react--flask-project

To install:

1. clone the repository

    ```sh
    git clone https://github.com/pascalpoizat/template-reactflask-project
    ```

2. setup the backend

    ```sh
    cd template-reactflask-project/backend
    python3 -m venv venv
    source venv/bin/activate
    pip3 install python-dotenv flask
    ```

3. check the backend is ok

    ```sh
    venv/bin/flask run
    ```

    and then open `http://localhost:5000/time` (it should work and display time)

4. setup the frontend

    ```sh
    cd template-reactflask-project/frontend
    npm install
    ```

5. check the frontend is ok

    ```sh
    yarn start
    ```

    and then open `http://localhost:3000` (it should work, with time displayed as 0)

6. make all work

    ```sh
   cd template-reactflask-project/frontend; yarn start-api &; yarn start 
    ```

    and then open `http://localhost:3000` (it should work and display time)
