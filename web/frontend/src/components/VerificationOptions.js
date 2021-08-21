import React, { Component } from "react";
import { Checkbox } from "@material-ui/core";
import Tooltip from "@material-ui/core/Tooltip";
import { createMuiTheme } from "@material-ui/core/styles";
import Typography from "@material-ui/core/Typography";
import Paper from "@material-ui/core/Paper";
import Popper from "@material-ui/core/Popper";
import { withStyles } from "@material-ui/styles";

const theme = createMuiTheme({
  spacing: 2,
});

const styles = {
  typography: {
    padding: theme.spacing(2),
  },
};

class VerificationOptions extends Component {
  constructor(props) {
    super(props);
    this.state = {
      networks: [],
      networksChecked: [],
      properties: [],
      propertiesChecked: [],
      constraintNode: [],
      constraintEdge: [],
      anchorEl: null,
      open: false,
    };
  }

  componentDidMount() {
    this.setState({
      networks: [
        {
          name: "networks",
          value: "Network01Bag",
          text: "Bag",
          tooltiptext: "Unordered communication",
        },
        {
          name: "networks",
          value: "Network02FifoPair",
          text: "FifoPair",
          tooltiptext:
            "Fifo between each couple of processes (array of queues)",
        },
        {
          name: "networks",
          value: "Network03Causal ",
          text: "Causal",
          tooltiptext: "Causal communication, implemented with vector clocks.",
        },
        {
          name: "networks",
          value: "Network04Inbox",
          text: "Inbox",
          tooltiptext: "Input queue at each process where messages are added.",
        },
        {
          name: "networks",
          value: "Network05Outbox",
          text: "Outbox",
          tooltiptext:
            "Output queue at each process from where messages are fetched.",
        },
        {
          name: "networks",
          value: "Network06Fifo",
          text: "Fifo",
          tooltiptext: "Unique shared queue.",
        },
        {
          name: "networks",
          value: "Network07RSC",
          text: "RSC",
          tooltiptext: "Realizable with synchronous communication.",
        },
      ],
      networksChecked: ["Network01Bag"],
      properties: [
        {
          name: "properties",
          value: "Prop01Type",
          text: "Type",
          tooltiptext: "Check well-formedness and compute total state space.",
        },
        {
          name: "properties",
          value: "Prop02Safe",
          text: "Safe",
          tooltiptext: "No sequence flow edge has more than one token.",
        },
        {
          name: "properties",
          value: "Prop03Sound",
          text: "Sound",
          tooltiptext:
            "A process is sound if there are no token on inside edges, and one token only on EndEvents. A collaboration is sound if all processes are sound and there are no undelivered messages.",
        },
        {
          name: "properties",
          value: "Prop04MsgSound",
          text: "MsgSound",
          tooltiptext: "Like Sound, but ignore messages in transit.",
        },
      ],
      propertiesChecked: ["Prop01Type"],
      constraintNode: [
        { value: "TRUE", text: "None" },
        { value: "MaxNodeMarking1", text: "At most 1 token on nodes" },
        { value: "MaxNodeMarking2", text: "At most 2 token on nodes" },
        { value: "MaxNodeMarking3", text: "At most 3 token on nodes" },
      ],
      constraintEdge: [
        { value: "TRUE", text: "None" },
        { value: "MaxEdgeMarking1", text: "At most 1 token on edges" },
        { value: "MaxEdgeMarking2", text: "At most 2 token on edges" },
        { value: "MaxEdgeMarking3", text: "At most 3 token on edges" },
        {
          value: "MaxMessageEdgeMarking1",
          text: "At most 1 token on message edges",
        },
        {
          value: "MaxMessageEdgeMarking2",
          text: "At most 2 token on message edges",
        },

        {
          value: "MaxMessageEdgeMarking3",
          text: "At most 3 token on message edges",
        },
        {
          value: "MaxSequenceEdgeMarking1",
          text: "At most 1 token on sequence edges",
        },

        {
          value: "MaxSequenceEdgeMarking2",
          text: "At most 2 token on sequence edges",
        },

        {
          value: "MaxSequenceEdgeMarking3",
          text: "At most 3 token on sequence edges",
        },
      ],
    });
  }

  flipOpen = () => this.setState({ open: !this.state.open });

  handleClick = (event) => {
    this.state.ancherEl
      ? this.setState({ anchorEl: null })
      : this.setState({ anchorEl: event.currentTarget });
    this.flipOpen();
  };

  handleNetworksChange = (event) => {
    let net = event.target.value;
    if (!this.state.networksChecked.includes(net)) {
      this.setState({
        networksChecked: [...this.state.networksChecked, net],
      });
    } else {
      this.setState({
        networksChecked: this.state.networksChecked.filter((item) => {
          return item !== event.target.value;
        }),
      });
    }
  };

  handlePropertiesChange = (event) => {
    let prop = event.target.value;
    if (!this.state.propertiesChecked.includes(prop)) {
      this.setState({
        propertiesChecked: [...this.state.propertiesChecked, prop],
      });
    } else {
      this.setState({
        propertiesChecked: this.state.propertiesChecked.filter((item) => {
          return item !== event.target.value;
        }),
      });
    }
  };

  getConstraintNode = () => {};

  getConstraintEdge = () => {};

  render() {
    const id = this.state.open ? "simple-popper" : null;
    const { classes } = this.props;
    const { networks, properties, constraintNode, constraintEdge } = this.state;

    let networksList =
      networks.length > 0 &&
      networks.map((item, i) => {
        return (
          <div>
            <Checkbox
              key={i}
              name={item.name}
              value={item.value}
              checked={this.state.networksChecked.includes(item.value)}
              onChange={this.handleNetworksChange}
            />
            <Tooltip title={item.tooltiptext} placement="right">
              <a href>{item.text}</a>
            </Tooltip>
          </div>
        );
      }, this);

    let propertiesList =
      properties.length > 0 &&
      properties.map((item, i) => {
        return (
          <div>
            <Checkbox
              key={i}
              name={item.name}
              value={item.value}
              checked={this.state.propertiesChecked.includes(item.value)}
              onChange={this.handlePropertiesChange}
            />
            <Tooltip title={item.tooltiptext} placement="left">
              <a href>{item.text}</a>
            </Tooltip>
          </div>
        );
      }, this);

    let constraintsNodeList =
      constraintNode.length > 0 &&
      constraintNode.map((item, i) => {
        return (
          <option key={i} value={item.value}>
            {item.text}
          </option>
        );
      }, this);

    let constraintsEdgeList =
      constraintEdge.length > 0 &&
      constraintEdge.map((item, i) => {
        return (
          <option key={i} value={item.value}>
            {item.text}
          </option>
        );
      }, this);

    return (
      <div>
        <span
          id="parameters-verif-nav"
          onClick={(event) => this.handleClick(event)}
        >
          Verification options
        </span>
        <Popper
          placement="bottom"
          id={id}
          open={this.state.open}
          anchorEl={this.state.anchorEl}
        >
          <Paper>
            <Typography className={classes.typography}></Typography>
            <div className={classes.paper} id="choices">
              <div id="properties-choice">
                <h2 className="choice-title"> Properties </h2>
                {propertiesList}
              </div>
              <div id="networks-choice">
                <h2 className="choice-title"> Communication semantics </h2>
                <div id="basic-networks">
                  <h3 className="network-type-title"> Base semantics </h3>
                  {networksList}
                </div>
              </div>

              <div id="constraints-choice">
                <h2 className="choice-title"> Constraints </h2>
                <div>
                  Constraint on nodes:
                  <br></br>
                  <select id="ConstraintNode">{constraintsNodeList}</select>
                </div>
                <div>
                  Constraint on edges:
                  <br></br>
                  <select id="ConstraintEdge">{constraintsEdgeList}</select>
                </div>
              </div>
            </div>
          </Paper>
        </Popper>
      </div>
    );
  }
}

export default withStyles(styles)(VerificationOptions);
