import React, { Component } from "react";
import VerificationDetail from "./VerificationDetail";
import Table from "@material-ui/core/Table";
import TableBody from "@material-ui/core/TableBody";
import TableCell from "@material-ui/core/TableCell";
import TableContainer from "@material-ui/core/TableContainer";
import TableHead from "@material-ui/core/TableHead";
import TableRow from "@material-ui/core/TableRow";
import { BsTrash } from "react-icons/bs";

const urlVerification = "http://localhost:5000/api/verifications";

function createData(id, status, value, date) {
  return { id, status, value, date };
}
class Verifications extends Component {
  constructor(props) {
    super(props);
    this.state = {
      id: "",
      status: "",
      date: "",
      rows: [],
      rowSelected: null,
      suppress: false,
      index: null,
    };
  }

  async componentDidMount() {
    let response = await fetch(urlVerification);
    let data = await response.json();
    this.setData(data);
  }

  async componentDidUpdate(prevProps) {
    if (prevProps.dataFromParent !== this.props.dataFromParent) {
      let response = await fetch(urlVerification);
      let data = await response.json();
      this.updateData(data);
    }
    if (prevProps.statusLastVerif !== this.props.statusLastVerif) {
      this.updateLastStatusRow();
    }
    if (this.state.suppress) {
      this.setState({
        suppress: false,
      });
      this.deleteData();
    }
  }

  setData(data) {
    for (let r of data) {
      this.setState((state) => {
        const rows = state.rows.concat(
          createData(r.id, r.status, r.value, r.pub_date)
        );
        return {
          rows,
        };
      });
    }
  }

  updateData(data) {
    let i = data.length - 1;
    this.setState((state) => {
      const rows = state.rows.concat(
        createData(data[i].id, data[i].status, data[i].value, data[i].pub_date)
      );
      return {
        rows,
      };
    });
  }

  deleteData() {
    let i = this.state.index;
    this.setState((state) => {
      state.rows.splice(i, 1);
      state.rowSelected = i;
      const rows = state.rows;
      return {
        rows,
      };
    });
    this.forceUpdate();
  }

  updateLastStatusRow() {
    let i = this.state.rows.length - 1;
    let rows = [...this.state.rows];
    rows[i] = {
      ...rows[i],
      status: this.props.statusLastVerif,
      value: this.props.valueLastVerif,
    };
    this.setState({ rows });
  }

  render() {
    return (
      <div>
        <TableContainer
          style={{
            height: "90%",
            width: "25%",
            overflowY: "scroll",
            float: "left",
          }}
        >
          <Table aria-label="simple table">
            <TableHead>
              <TableRow>
                <TableCell>ID</TableCell>
                <TableCell>Status</TableCell>
                <TableCell>Value</TableCell>
                <TableCell>Date</TableCell>
              </TableRow>
            </TableHead>
            <TableBody>
              {this.state.rows
                .slice(0)
                .reverse()
                .map((row) => (
                  <TableRow
                    id={row.id}
                    key={row.id}
                    style={{
                      background:
                        row.id === this.state.rowSelected
                          ? "green"
                          : "transparent",
                    }}
                    onClick={() => {
                      this.setState({
                        rowSelected: row.id,
                      });
                    }}
                  >
                    <TableCell>{row.id}</TableCell>
                    <TableCell>{row.status}</TableCell>
                    <TableCell>{row.value}</TableCell>
                    <TableCell>{row.date}</TableCell>
                    <TableCell>
                      <button
                        onClick={() => {
                          fetch(urlVerification + `/${row.id}`, {
                            method: "DELETE",
                          });
                          this.setState({
                            suppress: true,
                            index: row.id - 1,
                          });
                        }}
                      >
                        <BsTrash></BsTrash>
                      </button>
                    </TableCell>
                  </TableRow>
                ))}
            </TableBody>
          </Table>
        </TableContainer>
        <div id="detail-verification">
          <VerificationDetail
            dataFromParent={this.state.rowSelected}
          ></VerificationDetail>
        </div>
      </div>
    );
  }
}

export default Verifications;
