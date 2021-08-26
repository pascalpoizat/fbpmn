import React from "react";
import Adapter from "enzyme-adapter-react-16";
import { shallow, configure } from "enzyme";
import CounterExample from "./CounterExample.js";
configure({ adapter: new Adapter() });

const stepsExpected = require("./expected/e001ClientSupplier.Network02FifoPair.Prop03Sound.js");

test("compare js from log2html with js from parseJSON of CounterExample.js", () => {
  const wrapper = shallow(<CounterExample></CounterExample>);
  let jsonfile = require("./observed/e001ClientSupplier.Network02FifoPair.Prop03Sound.json");
  expect(wrapper.instance().parseJSON(JSON.stringify(jsonfile.lcex))).toBe(
    stepsExpected()
  );
});
