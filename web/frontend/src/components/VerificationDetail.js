import React, { Component } from "react";
import BpmnJS from "bpmn-js/dist/bpmn-viewer.production.min.js";
import "bpmn-js/dist/assets/diagram-js.css";
import "bpmn-js/dist/assets/bpmn-font/css/bpmn.css";
import Results from "./Results";

const urlVerification = "http://localhost:5000/api/verifications/";

class VerificationDetail extends Component {
  constructor(props) {
    super(props);
    this.state = {
      modelContent: "",
      modelName: "",
      results: [],
      duration: null,
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
      this.resetStates();
      this.updateModel(this.props.dataFromParent);
      this.updateResults(this.props.dataFromParent);
    }
  }

  resetStates() {
    this.setState({
      modelContent: "",
      modelName: "",
      results: [],
      duration: null,
    });
  }

  updateResults(id) {
    const newUrl = `${urlVerification}${id}`;
    fetch(newUrl, { method: "GET" })
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          results: data.results,
          duration: data.duration,
        });
      });
  }

  updateModel(id) {
    const newUrlModel = `${urlVerification}${id}/model`;
    fetch(newUrlModel)
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          modelContent: data.content,
          modelName: data.name,
        });
        this.viewer.importXML(this.state.modelContent);
      })
      .catch((error) => {
        this.viewer.clear();
      });
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
        <Results
          verificationId={this.props.dataFromParent}
          duration={this.state.duration}
          modelName={this.state.modelName}
        ></Results>
      </div>
    );
  }
}

export default VerificationDetail;
