let steps = [];

function parseJSON(cex) {
  let cexJSON = JSON.parse(cex);
  var nodes;
  var edges;
  var net;
  for (let step of cexJSON) {
    if (step.sinfo !== "Stuttering") {
      nodes = tagCases(step.svalue.nodemarks);
      edges = tagCases(step.svalue.edgemarks);
      net = tagCases(step.svalue.net);
      setSteps(nodes, edges, net);
    }
  }
  return steps;
}

function tagCases(value) {
  switch (value.tag) {
    case "TupleValue":
      return tupleTagCase(value);
    case "MapValue":
      return mapTagCase(value);
    case "BagValue":
      return bagTagCase(value);
    default:
      return value.contents;
  }
}

function tupleTagCase(value) {
  if (value.contents.length === 0) {
    return [];
  } else {
    let tab = [];
    for (let i of value.contents) {
      tab.push(tagCases(i));
    }
    return tab;
  }
}

function mapTagCase(value) {
  if (value.contents.size === 0) {
    return new Map([]);
  } else {
    let map = new Map();
    for (let k in value.contents) {
      map.set(k, tagCases(value.contents[k]));
    }
    return new Map(map);
  }
}

function bagTagCase(value) {
  if (value.contents.length === 0) {
    return new Map([[[]]]);
  } else {
    let map = new Map();
    let key = [];
    let valu = [];
    for (let i of value.contents) {
      key = tagCases(i[0]);
      valu = tagCases(i[1]);
      map.set(key, valu);
    }
    return new Map(map);
  }
}

function setSteps(nodes, edges, net) {
  steps.push([nodes, edges, net]);
}

module.exports = parseJSON;
