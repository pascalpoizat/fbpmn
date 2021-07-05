import React from "react";
import Popper from "@material-ui/core/Popper";
import { makeStyles } from "@material-ui/core/styles";

let output = "";

function setOutput() {
  fetch("http://localhost:5000/verifications/latest")
    .then((res) => res.json())
    .then((data) => {
      output = data.output;
    });
}

const useStyles = makeStyles((theme) => ({
  paper: {
    border: "1px solid",
    padding: theme.spacing(1),
    backgroundColor: theme.palette.background.paper,
  },
}));

export default function Verification() {
  const classes = useStyles();
  const [anchorEl, setAnchorEl] = React.useState(null);

  const handleClick = (event) => {
    setAnchorEl(anchorEl ? null : event.currentTarget);
    setOutput();
  };

  const open = Boolean(anchorEl);
  const id = open ? "simple-popper" : undefined;
  return (
    <div>
      <a aria-describedby={id} type="button" onClick={handleClick}>
        Verification Output
      </a>
      <Popper
        placement="bottom"
        id={id}
        open={open}
        anchorEl={anchorEl}
        modifiers={{
          flip: {
            enabled: true,
          },
          preventOverflow: {
            enabled: true,
            boundariesElement: "scrollParent",
          },
          arrow: {
            enabled: true,
          },
        }}
      >
        <div className={classes.paper}>{output}</div>
      </Popper>
    </div>
  );
}
