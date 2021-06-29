import React from "react";
import "./App.css";
import Verify from "./components/Verify.js";
import Verification from "./components/Verification.js";
import About from "./components/About.js";
import BpmnModelerComponent from "./components/bpmn/bpmn.modeler.component";

function App() {
  return (
    <div>
      <div id="settings">
        <Verify></Verify>
        <Verification></Verification>
        <About></About>
      </div>
      <BpmnModelerComponent></BpmnModelerComponent>
    </div>
  );
}

export default App;
