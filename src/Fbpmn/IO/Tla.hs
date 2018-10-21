module Fbpmn.IO.Tla where

import           Fbpmn.Model
import           Data.List                      ( intercalate )
import           Data.Map.Strict                ( (!?) )

{-|
Write a BPMN Graph to a TLA+ file.
-}
writeToTLA :: FilePath -> BpmnGraph -> IO ()
writeToTLA p = writeFile p . encodeBpmnGraphToTla

{-|
Transform a BPMN Graph to a TLA specification.
-}
encodeBpmnGraphToTla :: BpmnGraph -> String
encodeBpmnGraphToTla g =
  unlines
    $   [ encodeBpmnGraphHeaderToTla
        , encodeBpmnGraphProcessDeclToTla
        , encodeBpmnGraphContainRelToTla
        , encodeBpmnGraphNodeDeclToTla
        , encodeBpmnGraphFlowDeclToTla
        , encodeBpmnGraphMsgDeclToTla
        , encodeBpmnGraphCatNToTla
        , encodeBpmnGraphCatEToTla
        , encodeBpmnGraphFooterToTla
        ]
    <*> [g]

encodeBpmnGraphHeaderToTla :: BpmnGraph -> String
encodeBpmnGraphHeaderToTla g = unlines
  [ "---------------- MODULE " <> name g <> " ----------------"
  , ""
  , "EXTENDS TLC, PWSTypes"
  , ""
  , "VARIABLES nodemarks, edgemarks, net"
  , ""
  , "var == <<nodemarks, edgemarks, net>>"
  ]

encodeBpmnGraphFooterToTla :: BpmnGraph -> String
encodeBpmnGraphFooterToTla _ = unlines
  [ ""
  , "WF == INSTANCE PWSWellFormed"
  , "ASSUME WF!WellFormedness"
  , ""
  , "INSTANCE PWSSemantics"
  , ""
  , "Spec == Init /\\ [][Next]_var /\\ WF_var(Next)"
  , ""
  , "================================================================"
  ]

-- TODO: extend with multiple processes
encodeBpmnGraphProcessDeclToTla :: BpmnGraph -> String
encodeBpmnGraphProcessDeclToTla _ = "TopProcess == { \"" <> "Process" <> "\" }"

encodeBpmnGraphContainRelToTla :: BpmnGraph -> String
encodeBpmnGraphContainRelToTla _ = unlines []

encodeBpmnGraphNodeDeclToTla :: BpmnGraph -> String
encodeBpmnGraphNodeDeclToTla _ = unlines []

encodeBpmnGraphFlowDeclToTla :: BpmnGraph -> String
encodeBpmnGraphFlowDeclToTla g = unlines
  [ encodeBpmnGraphFlowDeclToTla' "NormalSeqFlowEdge" sequenceFlows g
  , encodeBpmnGraphFlowDeclToTla' "MsgFlowEdge"       messageFlows  g
  , "Edge == NormalSeqFlowEdge \\union MsgFlowEdge"
  ]

encodeBpmnGraphFlowDeclToTla' :: String
                              -> (BpmnGraph -> [Edge])
                              -> BpmnGraph
                              -> String
encodeBpmnGraphFlowDeclToTla' kindName flowFilter g =
  kindName <> " == {\n" <> intercalate ",\n" flowDecls <> "\t}\n"
 where
  flowDecls :: [String]
  flowDecls = flowToSeqFlowDeclaration <$> flowFilter g
  flowToSeqFlowDeclaration :: Edge -> String
  flowToSeqFlowDeclaration e =
    case
        do
          sourceNode <- sourceE g !? e
          targetNode <- targetE g !? e
          pure (sourceNode, targetNode)
      of
        Nothing      -> ""
        Just (n, n') -> "\t<<\"" <> n <> "\", \"" <> n' <> "\">>"

encodeBpmnGraphMsgDeclToTla :: BpmnGraph -> String
encodeBpmnGraphMsgDeclToTla _ = unlines []

encodeBpmnGraphCatNToTla :: BpmnGraph -> String
encodeBpmnGraphCatNToTla g = "CatN == "
  <> intercalate "\n@@ " (nodeToNodeCatDecl <$> nodes g)
 where
  nodeToNodeCatDecl :: Node -> String
  nodeToNodeCatDecl n = case catN g !? n of
    Nothing -> ""
    Just c  -> "\"" <> n <> "\"" <> " :> " <> toTLA c

encodeBpmnGraphCatEToTla :: BpmnGraph -> String
encodeBpmnGraphCatEToTla _ = unlines
  [ "CatE == [ e \\in Edge |->"
  , "  IF e \\in NormalSeqFlowEdge THEN NormalSeqFlow"
  , "  ELSE MsgFlow"
  ]

toTLA :: NodeType -> String
toTLA AbstractTask   = "AbstractTask"
toTLA SendTask       = "SendTask"
toTLA ReceiveTask    = "ReceiveTask"
toTLA SubProcess     = "SubProcess"
toTLA XorGateway     = "ExclusiveOr"
toTLA OrGateway      = "InclusiveOr"
toTLA AndGateway     = "Parallel"
toTLA NoneStartEvent = "StartEvent"
toTLA NoneEndEvent   = "EndEvent"
