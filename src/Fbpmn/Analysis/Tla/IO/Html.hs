{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.Analysis.Tla.IO.Html where

import           Fbpmn.Analysis.Tla.Model
import           NeatInterpolation              ( text )
import qualified Data.Text                     as T
import           Data.Map.Strict                ( (!?) )
import qualified Data.Map.Strict               as M
                                                ( toList )

{-|
Generates an HTML+JS animation for a log.
The model file must be in the same place than the log file.
-}
writeToHTML :: FilePath -> Maybe String -> Log -> IO ()
writeToHTML p _ = writeFile p . encodeLogToHtml

genSetup :: Log -> Text
genSetup (Log _ _ Success _) =
  [text|
  <!-- success log, nothing to generate -->
  |]
genSetup (Log _ _ Failure mcex) =
  case mcex of
    Nothing -> [text||] -- not possible
    Just cex -> foldMap genForState cex

genForState :: CounterExampleState -> Text
genForState s =
  if sinfo s /= "Stuttering"
    then
      [text|
        // step $ssid
        nodes = $sns;
        edges = $ses;
        net = $snet;
        steps.push([nodes, edges, net]);
      |]
    else [text||]      
  where
    ssid = show $ sid s
    sns = maybe "new Map([])" valueToJavascript (svalue s !? "nodemarks")
    ses = maybe "new Map([])" valueToJavascript (svalue s !? "edgemarks")
    snet = maybe "undefined" valueToJavascript (svalue s !? "net")

valueToJavascript :: Value -> Text
valueToJavascript (VariableValue v) = [text|"$sv"|] where sv = show v
valueToJavascript (IntegerValue i) = show i
valueToJavascript (StringValue s) = [text|"$sv"|] where sv = toText s
valueToJavascript (TupleValue xs) = [text|[$sxs]|]
    where
      sxs = T.intercalate ", " $ valueToJavascript <$> xs
valueToJavascript (SetValue xs) = [text|[$sxs]|]
    where
      sxs = T.intercalate ", " $ valueToJavascript <$> xs
valueToJavascript (MapValue xs) = [text|new Map([$sxs])|]
    where
      sxs = T.intercalate ", " $ f <$> M.toList xs
      f (var,val) = [text|["$svar", $sval]|]
        where
          svar = toText var
          sval = valueToJavascript val
valueToJavascript (BagValue xs) = [text|new Map([$sxs])|]
    where
      sxs = T.intercalate ", " $ f <$> M.toList xs
      f (val, n) = [text|[$sval, $sn]|]
        where
          sval = valueToJavascript val
          sn = valueToJavascript n

encodeLogToHtml :: Log -> Text
encodeLogToHtml l =
  let
    model = toText $ fromMaybe "noModel" $ lmodel l
    setup = genSetup l
  in
  [text|
  <!DOCTYPE html>
  <html>
    <head>
      <meta charset="UTF-8" />
      <title>fbpmn counter-example animator</title>
      <script>
        // model
        var diagramUrl = "$model";
        // elements to highlight
        var steps = [];
        var nodes;
        var edges;
        var net;
        $setup
      </script>
      <script src="https://unpkg.com/bpmn-js@3.3.1/dist/bpmn-viewer.development.js"></script>
      <script src="https://unpkg.com/jquery@3.3.1/dist/jquery.js"></script>
  
      <style>
        html, body {
          height: 100%;
          padding: 0;
          margin: 0;
        }
  
        #canvas {
          height: 90%;
          padding: 0;
          margin: 0;
        }
  
        #header {
          height: 10%;
          padding: 4;
          margin: 4;
          background: rgba(0,128,0,0.8);
          color: White;
        }
  
        #header #title {
          font-family: Arial, Helvetica, sans-serif;
          font-weight: bold;
          font-size: 3vh;
        }
  
        #header #step {
          font-family: Arial, Helvetica, sans-serif;
          font-weight: bold;
          font-size: 3vh;
        }
  
        .highlight-node:not(.djs-connection) .djs-visual > :nth-child(1) {
          fill: rgba(0,128,0,0.4) !important;
        }
  
        .highlight-edge:not(.djs-connection) .djs-visual > :nth-child(1) {
          stroke: rgba(0,128,0,0.8) !important;
        }
  
        .highlight-overlay {
          background-color: rgba(0,128,0,0.8) !important;
          pointer-events: none; /* no pointer events, allows clicking through onto the element */
        }
  
        .diagram-note {
          background-color:rgba(0,128,0,1) !important;
          color: White;
          border-color: Black;
          border-radius: 16px;
          font-family: Arial;
          font-size: 12px;
          padding: 2px;
          min-height: 16px;
          min-width: 16px;
          text-align: center;
        }
  
        .needs-discussion:not(.djs-connection) .djs-visual > :nth-child(1) {
          stroke: rgba(0,128,0,0.4) !important;
        }
      </style>
    </head>
    <body>
      <div id="header">
        <div id="title">&nbsp;fBPMN Counter Example Animator for $model</div>
        <div class="separator"><br/></div>
        <div id="step">step ../..</div>
      </div>
      <div id="canvas"></div>
      <script>
  
        // viewer instance
        var bpmnViewer = new BpmnJS({
          container: '#canvas'
        });
  
        function edgeBoundingBox(edge) {
          var minx,miny,maxx,maxy;
          if(edge.waypoints) {
            edge.waypoints.forEach(element => {
              var x = element.x;
              var y = element.y;
              if (x<minx || minx == undefined) { minx = x; }
              if (y<miny || miny == undefined) { miny = y; }
              if (x>maxx || maxx == undefined) { maxx = x; }
              if (y>maxy || maxy == undefined) { maxy = y; }
            });
          }
          return {minx: minx, miny: miny, maxx: maxx, maxy: maxy};
        }
  
        function markNode(canvas, node) {
          try {
            canvas.addMarker(node, 'highlight-node');
          }
          catch {}
        }
        function markEdge(canvas, edge) {
          try {
            canvas.addMarker(edge, 'highlight-edge');
          }
          catch {}
        }
        function unmarkNode(canvas, node) {
          try {
            canvas.removeMarker(node, 'highlight-node');
          }
          catch {}
        }
        function unmarkEdge(canvas, edge) {
          try {
            canvas.removeMarker(edge, 'highlight-edge');
          }
          catch {}
        }
        function showTokensNode(overlays, node, qty) {
          return overlays.add(node, 'note', {
              position: {top: -8,right: 8},
              html: '<div class="diagram-note">'+qty+'</div>'
            });
        }
        function showTokensEdge(registry, overlays, edge, qty) {
          var ee = registry.get(edge);
          var bb;
          var wp0;
          if (ee != undefined) {
            bb = edgeBoundingBox(ee);
            wp0 = ee.waypoints[0];
            dx = wp0.x - bb.minx;
            dy = wp0.y - bb.miny;
          }
          return overlays.add(edge, 'note', {
              position: {top: dy-10, left: dx-10},
              html: '<div class="diagram-note">'+qty+'</div>'
            });
        }
        // should be called with
        // 0 <= prestep <= nbstep-1
        // 0 <= step <= nbstep-1
        function animate(registry,canvas,overlays,csteps,markings,prestep,step,nbsteps) {
          // reset markings
          var ns = csteps[prestep][0];
          var es = csteps[prestep][1];
          if (prestep != step) {
            for(const k of ns.keys()) unmarkNode(canvas,k);
            for(const k of es.keys()) unmarkEdge(canvas,k);
            for(const id of markings) overlays.remove(id);
          }
          markings = [];
          // do new marking
          ns = csteps[step][0];
          es = csteps[step][1];
          // set
          for(const k of ns.keys()) {
            markNode(canvas,k);
          }
          for(const k of es.keys()) markNode(canvas,k);
          for (const [k,v] of ns) {
            try {
              var id = showTokensNode(overlays,k,v);
              markings.push(id);
            }
            catch {}
          }
          for (const [k,v] of es) {
            try {
              var id = showTokensEdge(registry,overlays,k,v);
              markings.push(id);
            }
            catch {}
          }
          return markings;
        }
  
        /**
          * Open diagram in our viewer instance.
          *
          * @param {String} bpmnXML diagram to display
          */
        function openDiagram(bpmnXML) {
  
          // import diagram
          bpmnViewer.importXML(bpmnXML, function(err) {
  
            if (err) {
              return console.error('could not import BPMN 2.0 diagram', err);
            }
  
            // access viewer components
            var canvas = bpmnViewer.get('canvas');
            var overlays = bpmnViewer.get('overlays');
            var registry = bpmnViewer.get('elementRegistry');
            // var moddle = bpmnViewer.get('moddle');
            // var model = bpmnViewer.getDefinitions();
  
            // zoom to fit full viewport
            canvas.zoom('fit-viewport');
  
            // animation variables
            var markings = [];
            var prestep = 0;
            var step = 0;
            nbsteps = steps.length;
            // first drawing
            markings = animate(registry,canvas,overlays,steps,markings,prestep,step,nbsteps);
  
            document.body.onkeyup = function(e){
              if(step < nbsteps-1 && e.keyCode == 39 && e.shiftKey == false){
                prestep = step;
                step = step+1;
                markings = animate(registry,canvas,overlays,steps,markings,prestep,step,nbsteps);
              }
              else if(step > 0 && e.keyCode == 37 && e.shiftKey == false) {
                prestep = step;
                step = step-1;
                markings = animate(registry,canvas,overlays,steps,markings,prestep,step,nbsteps);
              }
              else if(e.keyCode == 37 && e.shiftKey == true) {
                prestep = step;
                step = 0;
                markings = animate(registry,canvas,overlays,steps,markings,prestep,step,nbsteps);
              }
              else if(e.keyCode == 39 && e.shiftKey == true) {
                prestep = step;
                step = nbsteps-1;
                markings = animate(registry,canvas,overlays,steps,markings,prestep,step,nbsteps);
              }
              var title = "&nbsp;step " + (step+1) + "/" + nbsteps;
              $("#step").html(title); 
            }
  
          });
        }
  
  
        // load external diagram file via AJAX and open it
        $.get(diagramUrl, openDiagram, 'text');
      </script>
      <!--
        Thanks for trying out our BPMN toolkit!
  
        If you'd like to learn more about what our library,
        continue with some more basic examples:
        * https://github.com/bpmn-io/bpmn-js-examples/overlays
        * https://github.com/bpmn-io/bpmn-js-examples/interaction
        * https://github.com/bpmn-io/bpmn-js-examples/colors
        * https://github.com/bpmn-io/bpmn-js-examples/commenting
  
        To get a bit broader overview over how bpmn-js works,
        follow our walkthrough:
        * https://bpmn.io/toolkit/bpmn-js/walkthrough/
  
        Related starters:
        * https://raw.githubusercontent.com/bpmn-io/bpmn-js-examples/starter/modeler.html
      -->
    </body>
  </html>
    |]



