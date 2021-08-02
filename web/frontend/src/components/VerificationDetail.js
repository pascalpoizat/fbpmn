import React, { Component } from "react";
import BpmnJS from "bpmn-js/dist/bpmn-viewer.production.min.js";
import "bpmn-js/dist/assets/diagram-js.css";
import "bpmn-js/dist/assets/bpmn-font/css/bpmn.css";
import Results from "./Results";

const urlVerifications = "http://localhost:5000/verifications/";

/* récupère la vérification sélectionnée, actualise le modèle
fetch la vérification et retourne les urls de results à Results*/

class VerificationDetail extends Component {
  constructor(props) {
    super(props);
    this.state = {
      modelContent: "",
      results: [],
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
      this.updateResults(this.props.dataFromParent);
    }
  }

  updateResults(id) {
    const newUrl = `${urlVerifications}${id}`;
    fetch(newUrl, { method: "GET" })
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          results: data.results,
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
        <Results dataFromParent={this.state.results}></Results>
      </div>
    );
  }
}

export default VerificationDetail;
