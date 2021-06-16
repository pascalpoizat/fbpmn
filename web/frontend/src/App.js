import React, { useState, useEffect } from 'react';
import logo from './logo.svg';
import './App.css';

function App() {
  const [currentVersion, setCurrentVersion] = useState(0);

  useEffect(() => {
    fetch('/version').then(res => res.json()).then(data => {
      setCurrentVersion(data.version);
    });
  }, []);

  return (
    "fBPMN, v" + currentVersion
  );
}

export default App;
