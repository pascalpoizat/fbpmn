module Fbpmn
       ( someFunc
       , add
       ) where

someFunc :: IO ()
someFunc = putStrLn ("fBPMN: formal tools for BPMN" :: Text)

add :: Int -> Int -> Int
add x y = x + y
