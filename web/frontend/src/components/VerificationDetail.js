import React from "react";
import { Component } from "react";
import BpmnJS from "bpmn-js/dist/bpmn-viewer.production.min.js";
import "bpmn-js/dist/assets/diagram-js.css";
import "bpmn-js/dist/assets/bpmn-font/css/bpmn.css";

/* quand this.props.dataFromParent change => tous les autres this.state doivent changer */

class VerificationDetail extends Component {
  constructor(props) {
    super(props);
    const idVerification = this.props.dataFromParent.toString();
    this.state = {
      output: "",
      model_content: "",
      url: `http://localhost:5000/verifications/${idVerification}`,
      urlmodel: `http://localhost:5000/verifications/${idVerification}/model`,
    };
  }

  componentDidMount = () => {
    fetch(this.state.url)
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          output: data.output,
        });
      });
    fetch(this.state.urlmodel)
      .then((res) => res.json())
      .then((data) => {
        this.setState({
          model_content: data.content,
        });
      });
    this.viewer = new BpmnJS({
      container: "#model-viewer",
      keyboard: {
        bindTo: window,
      },
    });
    /*var { content } = this.state;
    this.viewer.importXML(content);*/
  };

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
          {this.state.output}
          {this.state.url}
        </div>
      </div>
    );
  }
}

export default VerificationDetail;
