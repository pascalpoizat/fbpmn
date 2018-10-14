-- import Gauge.Main
import           Criterion.Main

import           Fbpmn
import           Examples                       ( g1 )

main :: IO ()
main = defaultMain [bench "isValidGraph" (whnf isValidGraph g1)]

