import React from "react";
import "./App.css";
import Verification from "./components/Verification.js";
import About from "./components/About.js";
import BpmnModelerComponent from "./components/bpmn/bpmn.modeler.component";

function App() {
  return (
    <div>
      <div id="settings">
        <About></About>
        <Verification></Verification>
      </div>
      <BpmnModelerComponent></BpmnModelerComponent>
    </div>
  );
}

export default App;
