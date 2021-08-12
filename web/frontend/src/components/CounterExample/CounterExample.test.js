const stepsExpected = require("./expected/e001ClientSupplier.Network02FifoPair.Prop03Sound.js");

const parseJSON = require("./CounterExampleFunctions.js");

test("compare js from log2html with js from parseJSON of CounterExample.js", () => {
  let jsonfile = require("./observed/e001ClientSupplier.Network02FifoPair.Prop03Sound.json");
  expect(parseJSON(JSON.stringify(jsonfile.lcex))).toBe(stepsExpected());
});
