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
    <-! success log, nothing to generate -->
  |]
genSetup (Log _ _ Failure mcex) =
  case mcex of
    Nothing -> [text||] -- not possible
    Just cex -> foldMap genForState cex

genForState :: CounterExampleState -> Text
genForState s =
  [text|
    // step $ssid
    nodes = $sns;
    edges = $ses;
    steps.push([nodes, edges]);
  |]
  where
    ssid = show $ sid s
    sns = maybe "new Map([])" valueToJavascript (svalue s !? "nodemarks")
    ses = maybe "new Map([])" valueToJavascript (svalue s !? "edgemarks")

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
        //
        $setup
      </script>
  
      <!-- viewer distro (without pan and zoom) -->
      <!--
      <script src="https://unpkg.com/bpmn-js@3.3.1/dist/bpmn-viewer.development.js"></script>
      -->
      
      <!-- viewer distro (with pan and zoom) -->
      <script src="https://unpkg.com/bpmn-js@3.3.1/dist/bpmn-navigated-viewer.development.js"></script>
      <!-- <script src="bpmn-navigated-viewer.development.js"></script> -->
  
      <script src="https://unpkg.com/jquery@3.3.1/dist/jquery.js"></script>
      <!-- <script src="jquery-3.4.0.js"></script> -->
  
      <!-- example styles -->
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
          background: green;
          opacity: 0.8;
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
          fill: green !important;
          opacity: 0.4;
        }
  
        .highlight-edge:not(.djs-connection) .djs-visual > :nth-child(1) {
        }
  
        .highlight-overlay {
          background-color: green !important;
          opacity: 0.8;
          pointer-events: none; /* no pointer events, allows clicking through onto the element */
        }
  
        .diagram-note {
          background-color: green !important;
          opacity: 0.8;
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
          stroke: green !important;
          opacity: 0.8;
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
  
        function markNode(canvas, node) {
          canvas.addMarker(node, 'highlight-node');
        }
        function markEdge(canvas, edge) {
          canvas.addMarker(edge, 'highlight-edge');
        }
        function unmarkNode(canvas, node) {
          canvas.removeMarker(node, 'highlight-node');
        }
        function unmarkEdge(canvas, edge) {
          canvas.removeMarker(edge, 'highlight-edge');
        }
        function showTokensNode(overlays, node, qty) {
          return overlays.add(node, 'note', {
              position: {top: -8,right: 8},
              html: '<div class="diagram-note">'+qty+'</div>'
            });
        }
        function showTokensEdge(overlays, edge, qty) {
          return overlays.add(edge, 'note', {
              position: {top: -10, left: 0},
              html: '<div class="diagram-note">'+qty+'</div>'
            });
        }
        function animate(canvas,overlays,markings,prestep,step,nbsteps) {
          // reset markings
          var ns = steps[prestep][0];
          var es = steps[prestep][1];
          if (prestep != step) {
            for(const k of ns.keys()) unmarkNode(canvas,k);
            for(const k of es.keys()) unmarkEdge(canvas,k);
            for(const id of markings) overlays.remove(id);
          }
          markings = [];
          // do new marking
          ns = steps[step][0];
          es = steps[step][1];
          // set
          for(const k of ns.keys()) markNode(canvas,k);
          for(const k of es.keys()) markNode(canvas,k);
          for (const [k,v] of ns) {
            var id = showTokensNode(overlays,k,v);
            markings.push(id);
          }
          for (const [k,v] of es) {
            var id = showTokensEdge(overlays,k,v);
            markings.push(id);
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
  
            // zoom to fit full viewport
            canvas.zoom('fit-viewport');
  
            var markings = [];
            var prestep = 0;
            var step = 0;
            var nbsteps = steps.length;
            markings = animate(canvas,overlays,markings,prestep,step,nbsteps);
  
            document.body.onkeyup = function(e){
              if(step < nbsteps && e.keyCode == 39 && e.shiftKey == false){
                prestep = step;
                step = step+1;
                markings = animate(canvas,overlays,markings,prestep,step,nbsteps);
              }
              else if(step > 0 && e.keyCode == 37 && e.shiftKey == false) {
                prestep = step;
                step = step-1;
                markings = animate(canvas,overlays,markings,prestep,step,nbsteps);
              }
              else if(e.keyCode == 37 && e.shiftKey == true) {
                prestep = step;
                step = 0;
                markings = animate(canvas,overlays,markings,prestep,step,nbsteps);
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



