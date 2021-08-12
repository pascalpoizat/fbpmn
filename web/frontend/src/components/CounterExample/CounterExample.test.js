import React from "react";
import renderer from "react-test-renderer";
import CounterExample from "./CounterExample";

const sum = require("./CounterExample");

test("adds 1 + 2 to equal 3", () => {
  expect(sum(1, 2)).toBe(3);
});
