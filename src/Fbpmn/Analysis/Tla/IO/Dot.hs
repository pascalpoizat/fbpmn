{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.Analysis.Tla.IO.Dot where

import           Fbpmn.Analysis.Tla.Model
import           NeatInterpolation              ( text )
import           Data.Map.Strict                ( (!?) )
import qualified Data.Map.Strict               as M
                                                ( toList )
import qualified Data.Text                     as T
import Fbpmn.Helper (FWriter (FW))

-- | FWriter from TLA Log to DOT.
writer :: FWriter Log
writer = FW writeToDOT ".dot"

writeToDOT :: FilePath -> Log -> IO ()
writeToDOT p = writeFile p . toString . encodeLogToDot

encodeLogToDot :: Log -> Text
encodeLogToDot l =
  unlines
    $   [ encodeLogHeaderToDot    -- header
        , encodeLogNodeDeclToDot  -- nodes
        -- , encodeLogEdgeDeclToDot  -- edges
        , encodeLogFooterToDot    -- footer
        ]
    <*> [l]

encodeLogHeaderToDot :: Log -> Text
encodeLogHeaderToDot (Log _ m _ _) =
  [text|digraph $n {
    graph [rankdir = "LR"]; 
    node [fontsize = "18";shape = "record"];   
  |]
  where
    n = maybe "noName" show m

encodeLogFooterToDot :: Log -> Text
encodeLogFooterToDot _ =
  [text|}
  |]

encodeLogNodeDeclToDot :: Log -> Text
encodeLogNodeDeclToDot (Log _ _ Success Nothing) =
  [text|SUCCESS [label="SUCCESS"]|]
encodeLogNodeDeclToDot (Log _ _ Failure (Just cex)) =
  [text|
  $nes
  |]
  where
    nes = unlines $ encodeLogStateToDot <$> cex
encodeLogNodeDeclToDot _ = ""

encodeLogStateToDot :: CounterExampleState -> Text
encodeLogStateToDot (CounterExampleState sid _ svalue) =
  [text|$ssid [label="$ssid|$sns|$ses|$snet"]|]
  where
    ssid = show sid
    sns = maybe "" valueToDot (svalue !? "nodemarks")
    ses = maybe "" valueToDot (svalue !? "edgemarks")
    snet = maybe "" valueToDot (svalue !? "net")

valueToDot :: Value -> Text
valueToDot (VariableValue v) = show v
valueToDot (IntegerValue i) = show i
valueToDot (StringValue s) = toText s
valueToDot (TupleValue xs) = [text|\<\<$sxs\>\>|]
    where
      sxs = T.intercalate ", " $ valueToDot <$> xs
valueToDot (SetValue xs) = [text|\{$sxs\}|]
    where
      sxs = T.intercalate ", " $ valueToDot <$> xs
valueToDot (MapValue xs) = [text|\[$sxs\]|]
    where
      sxs = T.intercalate ", " $ f <$> M.toList xs
      f (var,val) = [text|$svar\|-\>$sval|]
        where
          svar = toText var
          sval = valueToDot val
valueToDot (BagValue xs) = [text|($sxs)|]
    where
      sxs = T.intercalate ", " $ f <$> M.toList xs
      f (val, n) = [text|$sval:\>$sn|]
        where
          sval = valueToDot val
          sn = valueToDot n
