import React from "react";
import { Component } from "react";
import BpmnJS from "bpmn-js/dist/bpmn-viewer.production.min.js";
import "bpmn-js/dist/assets/diagram-js.css";
import "bpmn-js/dist/assets/bpmn-font/css/bpmn.css";

const urlVerifications = "http://localhost:5000/verifications/";

class VerificationDetail extends Component {
  constructor(props) {
    super(props);
    this.state = {
      output: "",
      modelContent: "",
    };
  }

  componentDidMount = () => {
    this.viewer = new BpmnJS({
      container: "#model-viewer",
      keyboard: {
        bindTo: window,
      },
    });
  };

  componentDidUpdate(prevProps) {
    if (prevProps.dataFromParent !== this.props.dataFromParent) {
      this.updateModel(this.props.dataFromParent);
      this.updateOutput(this.props.dataFromParent);
    }
  }

  updateOutput(id) {
    const newUrl = `${urlVerifications}${id}`;
    fetch(newUrl, { method: "GET" })
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          output: data.output,
        });
      });
  }

  updateModel(id) {
    const newUrlModel = `${urlVerifications}${id}/model`;
    fetch(newUrlModel)
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          modelContent: data.content,
        });
        this.viewer.importXML(this.state.modelContent);
      })
      .catch((error) => {
        this.viewer.clear();
      });
  }

  displayOutput(output) {
    if (!this.props.dataFromParent) {
      console.log("no verification selected");
    } else {
      if (output) {
        let x = document.getElementById("output");
        output = output.substr(output.search("<<"));
        x.innerText = "Verification realized in .. s" + output;
      } else {
        let x = document.getElementById("output");
        x.innerText = "null";
      }
    }
  }

  render() {
    return (
      <div>
        <div
          id="model-viewer"
          style={{
            width: "30%",
            height: "94vh",
            float: "left",
          }}
        ></div>
        <div
          id="output"
          style={{
            width: "275px",
            height: "94vh",
            float: "right",
            maxHeight: "98vh",
            overflowX: "auto",
          }}
        >
          {this.displayOutput(this.state.output)}
        </div>
      </div>
    );
  }
}

export default VerificationDetail;
