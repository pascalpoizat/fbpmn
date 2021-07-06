import React from "react";
import { FaGithub } from "react-icons/fa";
import Link from "@material-ui/core/Link";
import Dialog from "@material-ui/core/Dialog";
import DialogContentText from "@material-ui/core/DialogContentText";
import DialogTitle from "@material-ui/core/DialogTitle";
import DialogContent from "@material-ui/core/DialogContent";

let version;

function setVersion() {
  fetch("http://localhost:5000/version")
    .then((res) => res.json())
    .then((data) => {
      version = data.major + "." + data.minor + "." + data.patch;
    });
}

setVersion();

export default function About() {
  const [open, setOpen] = React.useState(false);

  const handleClickToOpen = () => {
    setOpen(true);
  };

  const handleToClose = () => {
    setOpen(false);
  };

  return (
    <div>
      <a
        id="about-nav"
        onClick={() => {
          setVersion();
          handleClickToOpen();
        }}
      >
        About
      </a>
      <Dialog open={open} onClose={handleToClose}>
        <DialogTitle>fBPMN v{version}</DialogTitle>
        <DialogContent>
          <DialogContentText>
            This interface offers the verification of business processes
            (workflows and collaborations). It supports several properties
            (safety, soundness...), seven communication semantics. It is built
            upon{" "}
            <Link href="https://github.com/pascalpoizat/fbpmn" target="_blank">
              fbpmn <FaGithub></FaGithub>
            </Link>{" "}
            where documentation is available.
          </DialogContentText>
        </DialogContent>
      </Dialog>
    </div>
  );
}
