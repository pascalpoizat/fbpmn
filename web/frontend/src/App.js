import React from 'react'
import Dialog from "@material-ui/core/Dialog";
import DialogContentText from "@material-ui/core/DialogContentText";
import DialogTitle from "@material-ui/core/DialogTitle";
import DialogContent from "@material-ui/core/DialogContent";
import logo from './logo.svg';
import './App.css';

let version;

function setVersion() {
  fetch('/version').then(res => res.json()).then(data => {
    version = data.major + "." + data.minor + "." + data.patch
  });
}

function App() {
  const [open, setOpen] = React.useState(false);

  const handleClickToOpen = () => {
    setOpen(true);
  };

  const handleToClose = () => {
    setOpen(false);
  };

  setVersion();

  return (
    <div>
      <a id="about-nav" onClick={handleClickToOpen}>About</a>
      <Dialog open={open} onClose={handleToClose}>
        <DialogTitle>fBPMN v{version}</DialogTitle>
        <DialogContent>
          <DialogContentText>
            Version {version}
          </DialogContentText>
        </DialogContent>
      </Dialog>
    </div>
  );
}

export default App;
