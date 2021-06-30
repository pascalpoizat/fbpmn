import React from "react";
import { FaGithub } from "react-icons/fa";
import Link from "@material-ui/core/Link";
import Dialog from "@material-ui/core/Dialog";
import DialogContentText from "@material-ui/core/DialogContentText";
import DialogTitle from "@material-ui/core/DialogTitle";
import DialogContent from "@material-ui/core/DialogContent";

let version;

function setVersion() {
  fetch("/version")
    .then((res) => res.json())
    .then((data) => {
      version = data.major + "." + data.minor + "." + data.patch;
    });
}

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
        href
        onClick={() => {
          handleClickToOpen();
          setVersion();
        }}
      >
        About
      </a>
      <Dialog open={open} onClose={handleToClose}>
        <DialogTitle>fBPMN v{version}</DialogTitle>
        <DialogContent>
          <DialogContentText>
            Outil d'analyse de processus métiers. Code à retrouver sur{" "}
            <Link href="https://github.com/pascalpoizat/fbpmn" target="_blank">
              <FaGithub></FaGithub>
            </Link>
          </DialogContentText>
        </DialogContent>
      </Dialog>
    </div>
  );
}
