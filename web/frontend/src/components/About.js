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
      <span
        id="about-nav"
        onClick={() => {
          handleClickToOpen();
        }}
      >
        About
      </span>
      <Dialog open={open} onClose={handleToClose}>
        <DialogTitle>fBPMN v{version}</DialogTitle>
        <DialogContent>
          <DialogContentText>
            fBPMN Web application. Based on fbpmn version v{version}. fBPMN is a
            framework for the formal analysis of BPMN business process models
            (workflows and collaborations). See more information at {""}
            <Link href="https://github.com/pascalpoizat/fbpmn" target="_blank">
              https://github.com/pascalpoizat/fbpmn <FaGithub></FaGithub>
            </Link>{" "}
            where documentation is available.
          </DialogContentText>
        </DialogContent>
      </Dialog>
    </div>
  );
}
