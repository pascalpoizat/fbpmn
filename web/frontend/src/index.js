import React from "react";
import ReactDOM from "react-dom";
import { Route, BrowserRouter } from "react-router-dom";
import App from "./App";
import CounterExample from "./components/CounterExample";
import reportWebVitals from "./reportWebVitals";
import "./index.css";

const routs = (
  <BrowserRouter>
    <div>
      <Route exact path="/" component={App} />
      <Route path="/counter_examples/:id" exact component={CounterExample} />
    </div>
  </BrowserRouter>
);
const rootElement = document.getElementById("root");
ReactDOM.render(routs, rootElement);

// If you want to start measuring performance in your app, pass a function
// to log results (for example: reportWebVitals(console.log))
// or send to an analytics endpoint. Learn more: https://bit.ly/CRA-vitals
reportWebVitals();
