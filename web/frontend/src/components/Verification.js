import React from "react";
import Popup from "reactjs-popup";
import "reactjs-popup/dist/index.css";

let output;

function setOutput() {
  fetch("/verifications/3")
    .then((res) => res.json())
    .then((data) => {
      output = data.ouput;
    });
}

export default function Verification() {
  return (
    <div>
      <Popup
        trigger={
          <a href onClick={setOutput}>
            {" "}
            Verification Output
          </a>
        }
        position="bottom center"
      >
        <div>Output vérification: {output}</div>
      </Popup>
    </div>
  );
}
