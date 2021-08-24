import React, { Component } from "react";
import { DataGrid } from "@material-ui/data-grid";
import { Link } from "react-router-dom";
import { FaArrowRight } from "react-icons/fa";

const localhost = "http://localhost:3000";

function createData(id, comm, prop, value, counter_example) {
  if (value) {
    return { id, comm, prop, value };
  } else {
    value = `${localhost}${counter_example}`;
    return { id, comm, prop, value };
  }
}

const columns = [
  { field: "comm", headerName: "Communication", width: 118 },
  { field: "prop", headerName: "Property", width: 118 },
  {
    field: "value",
    headerName: "Value",
    width: 70,
    renderCell: (params) => (
      <div>
        {params.value !== true ? (
          <Link
            to={{
              pathname: params.value,
            }}
            target="_blank"
          >
            <FaArrowRight></FaArrowRight>
          </Link>
        ) : (
          <div>true</div>
        )}
      </div>
    ),
  },
];

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
      fetch(urlResult)
        .then((res) => res.json())
        .then((data) => {
          for (let result of data) {
            this.setState((state) => {
              const rows = state.rows.concat(
                createData(
                  result.id,
                  result.communication,
                  result.property,
                  result.value,
                  result.counter_example
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
          width: "325px",
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
        <div style={{ height: 575, width: "100%" }}>
          <DataGrid
            rows={this.state.rows}
            columns={columns}
            hideFooter={true}
          />
        </div>
      </div>
    );
  }
}

export default Results;
