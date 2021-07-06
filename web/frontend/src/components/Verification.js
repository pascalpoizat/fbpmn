import React from "react";
import Popover from "@material-ui/core/Popover";
import Typography from "@material-ui/core/Typography";
import { makeStyles } from "@material-ui/core/styles";

let output = "";

function setOutput() {
  fetch("http://localhost:5000/verifications/latest")
    .then((res) => res.json())
    .then((data) => {
      output = data.output;
    });
}

function displayOutput(text) {
  return text.split("\n").map((item, i) => <p key={i}>{item}</p>);
}

const useStyles = makeStyles((theme) => ({
  typography: {
    padding: theme.spacing(1),
    width: 260,
    height: 520,
  },
}));

setOutput();

export default function Verification() {
  const classes = useStyles();
  const [anchorEl, setAnchorEl] = React.useState(null);

  const handleClick = (event) => {
    setAnchorEl(anchorEl ? null : event.currentTarget);
    setOutput();
  };

  const handleClose = () => {
    setAnchorEl(null);
  };

  const open = Boolean(anchorEl);
  const id = open ? "simple-popper" : undefined;
  return (
    <div>
      <a aria-describedby={id} type="button" onClick={handleClick}>
        Verification Output
      </a>
      <Popover
        id={id}
        open={open}
        anchorEl={anchorEl}
        onClose={handleClose}
        anchorOrigin={{
          vertical: "bottom",
          horizontal: "center",
        }}
        transformOrigin={{
          vertical: "top",
          horizontal: "center",
        }}
      >
        <Typography className={classes.typography}>
          {displayOutput(output)}
        </Typography>
      </Popover>
    </div>
  );
}
