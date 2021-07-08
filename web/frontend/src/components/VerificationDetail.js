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

  updateOutput(url) {
    const newUrl = `${urlVerifications}${url}`;
    fetch(newUrl)
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          output: data.output,
        });
      });
  }

  updateModel(url) {
    const newUrlModel = `${urlVerifications}${url}/model`;
    fetch(newUrlModel)
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          modelContent: data.content,
        });
        this.viewer.importXML(this.state.modelContent);
      });
  }

  render() {
    return (
      <div>
        <div
          id="model-viewer"
          style={{
            width: "60%",
            height: "94vh",
            float: "left",
          }}
        ></div>
        <div
          id="output"
          style={{
            width: "20%",
            height: "94vh",
            float: "right",
            maxHeight: "98vh",
            overflowX: "auto",
          }}
        >
          {this.props.dataFromParent}
        </div>
      </div>
    );
  }
}

export default VerificationDetail;
