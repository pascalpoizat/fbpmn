import React, { Component } from "react";
import { Link } from "react-router-dom";
import { FaArrowRight } from "react-icons/fa";

const urlCounterExample = "http://localhost:3000/counter-example/";

class Result extends Component {
  constructor(props) {
    super(props);
    this.state = {
      comm: "",
      prop: "",
      value: "",
      counter_example_id: "",
    };
  }

  componentDidMount = () => {
    this.setProperties(
      this.props.comm,
      this.props.prop,
      this.props.value,
      this.props.counter_example
    );
  };

  setProperties(comm, prop, value, counter_example) {
    this.setState({
      comm: comm,
      prop: prop,
      value: value,
      counter_example_id: counter_example,
    });
  }

  displayValue() {
    if (!this.state.value) {
      return "[ ]";
    } else {
      return "[X]";
    }
  }

  linkToCounterExample() {
    if (!this.state.value) {
      return (
        <button>
          <Link
            to={{
              pathname: `${urlCounterExample}${this.state.counter_example_id}`,
              state: { foo: "bar" },
            }}
            target="_blank"
          >
            <FaArrowRight></FaArrowRight>
          </Link>
        </button>
      );
    }
  }

  render() {
    return (
      <p>
        {this.displayValue()}
        {this.state.comm}.{this.state.prop}
        {this.linkToCounterExample()}
      </p>
    );
  }
}

export default Result;
