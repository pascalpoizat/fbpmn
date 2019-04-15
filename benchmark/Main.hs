-- import Gauge.Main
import           Criterion.Main

import           Fbpmn.BpmnGraph.Model
import           Examples                       ( g1 )

main :: IO ()
main = defaultMain [bench "isValidGraph" (whnf isValidGraph g1)]

