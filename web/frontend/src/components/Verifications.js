import React from "react";
import ReactDOM from "react-dom";
import { Component } from "react";
import VerificationDetail from "./VerificationDetail";
import Table from "@material-ui/core/Table";
import TableBody from "@material-ui/core/TableBody";
import TableCell from "@material-ui/core/TableCell";
import TableContainer from "@material-ui/core/TableContainer";
import TableHead from "@material-ui/core/TableHead";
import TableRow from "@material-ui/core/TableRow";

function createData(id, status) {
  return { id, status };
}

const url = "http://localhost:5000/verifications";

class Verifications extends Component {
  constructor(props) {
    super(props);
    this.state = {
      id: "",
      status: "",
      rows: [],
      row: "",
    };
  }

  async componentDidMount() {
    let response = await fetch(url);
    let data = await response.json();
    this.setData(data);
  }

  showVerif() {
    const rootElement = document.getElementById("detail-verification");
    const detail = <VerificationDetail dataFromParent={this.state.id} />;
    ReactDOM.render(detail, rootElement);
  }

  setData(data) {
    for (let r of data) {
      this.setState((state) => {
        const rows = state.rows.concat(state.row);
        return {
          rows,
          row: createData(r.id, r.status),
        };
      });
    }
    console.log(this.state.rows);
  }

  render() {
    return (
      <div>
        <TableContainer style={{ width: "20%", float: "left" }}>
          <Table aria-label="simple table">
            <TableHead>
              <TableRow>
                <TableCell>ID</TableCell>
                <TableCell>Status</TableCell>
              </TableRow>
            </TableHead>
            <TableBody>
              {this.state.rows.map((row) => (
                <TableRow
                  onClick={() => {
                    this.setState({
                      id: row.id,
                    });
                    this.showVerif();
                  }}
                  key={row.id}
                >
                  <TableCell>{row.id}</TableCell>
                  <TableCell>{row.status}</TableCell>
                </TableRow>
              ))}
            </TableBody>
          </Table>
        </TableContainer>
        <div id="detail-verification"></div>
      </div>
    );
  }
}

export default Verifications;
