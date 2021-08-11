import React, { Component } from "react";
import Result from "./Result";

function createData(comm, prop, value, counter_example) {
  return { comm, prop, value, counter_example };
}
class Results extends Component {
  constructor(props) {
    super(props);
    this.state = {
      rows: [],
    };
  }

  componentDidMount = () => {
    this.initiateRows();
  };

  componentDidUpdate(prevProps) {
    if (prevProps.verificationId !== this.props.verificationId) {
      this.resetRows();
      this.initiateRows();
    }
  }

  resetRows() {
    this.setState(() => {
      let rows = [];
      return {
        rows,
      };
    });
  }

  initiateRows() {
    if (this.props.verificationId) {
      const urlResult = `http://localhost:5000/verifications/${this.props.verificationId}/results`;
      console.log(urlResult);
      fetch(urlResult)
        .then((res) => res.json())
        .then((data) => {
          for (let result of data) {
            this.setState((state) => {
              const rows = state.rows.concat(
                createData(
                  result.communication,
                  result.property,
                  result.value,
                  result.counter_example_id
                )
              );
              return {
                rows,
              };
            });
          }
        });
    }
  }

  displayDuration() {
    if (this.props.duration) {
      return `Verification realized in ${this.props.duration} seconds`;
    }
  }

  render() {
    return (
      <div
        style={{
          width: "285px",
          height: "94vh",
          float: "right",
          maxHeight: "98vh",
          overflowX: "auto",
        }}
      >
        <h4>
          <center>
            <b>{this.props.modelName}</b>
          </center>
        </h4>
        <p> {this.displayDuration()}</p>
        {this.state.rows.map((row) => (
          <Result
            comm={row.comm}
            prop={row.prop}
            value={row.value}
            counter_example={row.counter_example}
          ></Result>
        ))}
      </div>
    );
  }
}

export default Results;
