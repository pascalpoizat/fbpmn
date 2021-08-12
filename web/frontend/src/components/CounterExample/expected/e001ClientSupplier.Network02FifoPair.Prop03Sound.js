// model
var diagramUrl = "e001ClientSupplier.bpmn";
// elements to highlight
var steps = [];
var nodes;
var edges;
var net;

// step 1
nodes = new Map([
  ["cStart", 1],
  ["sStart", 1],
]);
edges = new Map([]);
net = [];

steps.push([nodes, edges, net]);
// step 2
nodes = new Map([
  ["Supplier_", 1],
  ["cStart", 1],
]);
edges = new Map([["sE1", 1]]);
net = [];

steps.push([nodes, edges, net]);
// step 3
nodes = new Map([
  ["Supplier_", 1],
  ["cStart", 1],
  ["sReceiveCommand", 1],
]);
edges = new Map([]);
net = [];

steps.push([nodes, edges, net]);
// step 4
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["sReceiveCommand", 1],
]);
edges = new Map([["cE1", 1]]);
net = [];

steps.push([nodes, edges, net]);
// step 5
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cSendCommand", 1],
  ["sReceiveCommand", 1],
]);
edges = new Map([]);
net = [];

steps.push([nodes, edges, net]);
// step 6
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["sReceiveCommand", 1],
]);
edges = new Map([
  ["cE2", 1],
  ["mf1", 1],
]);
net = new Map([[["Client_", "Supplier_"], ["command"]]]);

steps.push([nodes, edges, net]);
// step 7
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
]);
edges = new Map([
  ["cE2", 1],
  ["sE2", 1],
]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 8
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
]);
edges = new Map([
  ["cE2", 1],
  ["sE3", 1],
  ["sE4", 1],
]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 9
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["sPrepareCommand", 1],
]);
edges = new Map([
  ["cE2", 1],
  ["sE4", 1],
]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 10
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cStoreRequest", 1],
  ["sPrepareCommand", 1],
]);
edges = new Map([["sE4", 1]]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 11
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cStoreRequest", 1],
]);
edges = new Map([
  ["sE4", 1],
  ["sE5", 1],
]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 12
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cStoreRequest", 1],
  ["sInvoiceManagement", 1],
]);
edges = new Map([["sE5", 1]]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 13
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cStoreRequest", 1],
]);
edges = new Map([
  ["sE5", 1],
  ["sE6", 1],
]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 14
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cStoreRequest", 1],
]);
edges = new Map([["sE7", 1]]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 15
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cStoreRequest", 1],
  ["sShipCommand", 1],
]);
edges = new Map([]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 16
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["sShipCommand", 1],
]);
edges = new Map([["cE3", 1]]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 17
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cReceiveInvoice", 1],
  ["sShipCommand", 1],
]);
edges = new Map([]);
net = new Map([[["Client_", "Supplier_"], []]]);

steps.push([nodes, edges, net]);
// step 18
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cReceiveInvoice", 1],
]);
edges = new Map([
  ["mf3", 1],
  ["sE8", 1],
]);
net = new Map([
  [["Client_", "Supplier_"], []],
  [["Supplier_", "Client_"], ["goods"]],
]);

steps.push([nodes, edges, net]);
// step 19
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cReceiveInvoice", 1],
  ["sSendInvoice", 1],
]);
edges = new Map([["mf3", 1]]);
net = new Map([
  [["Client_", "Supplier_"], []],
  [["Supplier_", "Client_"], ["goods"]],
]);

steps.push([nodes, edges, net]);
// step 20
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cReceiveInvoice", 1],
]);
edges = new Map([
  ["mf2", 1],
  ["mf3", 1],
  ["sE9", 1],
]);
net = new Map([
  [["Client_", "Supplier_"], []],
  [
    ["Supplier_", "Client_"],
    ["goods", "invoice"],
  ],
]);

steps.push([nodes, edges, net]);
// step 21
nodes = new Map([
  ["Client_", 1],
  ["Supplier_", 1],
  ["cReceiveInvoice", 1],
  ["sEnd", 1],
]);
edges = new Map([
  ["mf2", 1],
  ["mf3", 1],
]);
net = new Map([
  [["Client_", "Supplier_"], []],
  [
    ["Supplier_", "Client_"],
    ["goods", "invoice"],
  ],
]);

steps.push([nodes, edges, net]);

function stepsExpected() {
  return steps;
}

module.exports = stepsExpected;
