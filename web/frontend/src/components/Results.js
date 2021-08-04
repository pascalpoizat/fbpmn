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
    this.initiateRows(this.props.dataFromParent);
  };

  componentDidUpdate(prevProps) {
    if (prevProps.dataFromParent !== this.props.dataFromParent) {
      this.resetRows();
      this.initiateRows(this.props.dataFromParent);
    }
  }

  resetRows() {
    this.setState((state) => {
      state.rows = [];
    });
  }
  initiateRows(results) {
    if (results) {
      for (let result of results) {
        const urlResult = `http://localhost:5000${result}`;
        fetch(urlResult)
          .then((res) => res.json())
          .then((data) => {
            this.setState((state) => {
              const rows = state.rows.concat(
                createData(
                  data.communication,
                  data.property,
                  data.value,
                  data.counter_example_id
                )
              );
              return {
                rows,
              };
            });
          });
      }
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
