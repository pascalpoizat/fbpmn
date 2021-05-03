module Fbpmn.Helper
  ( module Fbpmn.Helper,
    module Data.Attoparsec.Text,
  )
where

import Data.Attoparsec.Text (Parser, Result, anyChar, char, decimal, digit, letter, manyTill, sepBy, space, string, parse, parseOnly, eitherResult, endOfLine, atEnd, inClass, satisfy)
import qualified Data.Attoparsec.Text as A (takeWhile)
import Data.Containers.ListUtils (nubOrd)
import Data.Map.Strict (keys, (!?))
import qualified Data.Set as S (fromList)
import qualified Data.Map.Strict as M (fromList, toList)

type TEither = Either Text

data FReader a = FR
  { read :: FilePath -> IO (TEither a),
    rsuffix :: Text
  }

data FWriter a = FW
  { write :: FilePath -> a -> IO (),
    wsuffix :: Text
  }

ith1 :: (a, b, c) -> a
ith1 (a, _, _) = a

ith2 :: (a, b, c) -> b
ith2 (_, b, _) = b

ith3 :: (a, b, c) -> c
ith3 (_, _, c) = c

appliedIsJust :: (a -> b -> Maybe c) -> (a -> b -> Bool)
appliedIsJust f a = isJust . f a

mapMap :: Ord a => (a -> Maybe b -> Maybe c) -> Map a b -> [c]
mapMap g m = catMaybes $ mapMapElement g m <$> keys m

mapMapElement :: Ord a => (a -> Maybe b -> Maybe c) -> Map a b -> a -> Maybe c
mapMapElement g m k = g k (m !? k)

liftMaybe1 :: (Maybe a, b) -> Maybe (a, b)
liftMaybe1 (Just a, b) = Just (a,b)
liftMaybe1 (Nothing, _) = Nothing

liftMaybe2 :: (a, Maybe b) -> Maybe (a, b)
liftMaybe2 (a, Just b) = Just (a, b)
liftMaybe2 (_, Nothing) = Nothing

mapMaybes :: Ord k => Map k (Maybe b) -> Map k b
mapMaybes m = M.fromList . catMaybes $ liftMaybe2 <$> M.toList m

filter' :: (Ord a) => [a] -> Map a b -> (Maybe b -> Bool) -> [a]
filter' xs f p = filter p' xs where p' x = p $ f !? x

filterKey :: Ord a => (a -> Bool) -> Map a b -> Map a b
filterKey p m = M.fromList $ filter (p . fst) $ M.toList m

filterValue :: Ord a => (b -> Bool) -> Map a b -> Map a b
filterValue p m = M.fromList $ filter (p . snd) $ M.toList m

-- | Checks whether all elements of a list are different.
allDifferent :: (Ord a) => [a] -> Bool
allDifferent xs = length xs == (length . nubOrd $ xs)

-- | Checks whether two lists are disjoint (no common elements).
disjoint :: (Eq a) => [a] -> [a] -> Bool
disjoint xs ys = not (any (`elem` ys) xs)

-- | applyFanout version of disjoint.
disjoint' :: (Eq a) => (b -> [a]) -> (b -> [a]) -> b -> Bool
disjoint' = applyFanout disjoint

-- | Combines the elements of a list with their indexes.
withIndex :: [a] -> [(Natural, a)]
withIndex = f 0
  where
    f _ [] = []
    f n (x : xs) = (n, x) : f (n + 1) xs

-- | Builds indexes for elements of a list (using withIndex).
withPrefixedIndex :: Text -> [a] -> [(Text, a)]
withPrefixedIndex p xs = prefix <$> withIndex xs
  where
    prefix (i, v) = (p <> show i, v)

-- | Given two lists, xs and ys, checks whether xs includes all elements of ys.
includesAll :: (Eq a) => [a] -> [a] -> Bool
includesAll xs = all (`elem` xs)

-- | applyFanout version of includesAll.
includesAll' :: (Eq a) => (b -> [a]) -> (b -> [a]) -> b -> Bool
includesAll' = applyFanout includesAll

-- | Given two lists, xs and ys, checks whether all elements in xs are in ys.
allIn :: (Eq a) => [a] -> [a] -> Bool
allIn = flip includesAll

-- | applyFanout version of allIn.
allIn' :: (Eq a) => (b -> [a]) -> (b -> [a]) -> b -> Bool
allIn' = applyFanout allIn

-- | Given a list xs and a map m, checks whether all elements in xs are keys in m.
allKeyIn :: (Eq a) => [a] -> Map a b -> Bool
allKeyIn ks m = ks `allIn` keys m

-- | applyFanout version of allKeyIn.
allKeyIn' :: (Eq a) => (b -> [a]) -> (b -> Map a c) -> b -> Bool
allKeyIn' = applyFanout allKeyIn

applyFanout :: (b1 -> b2 -> c) -> (a -> b1) -> (a -> b2) -> a -> c
applyFanout f g h = uncurry f . (g &&& h)

type Id = String

-- | Parse a container.
-- Can be used for different kinds of containers in different languages.
-- - parseContainer "[" "]" "," parseInteger for [1, 2, 3] lists
-- - parseContainer "{" "}" ";" parseString for {"1"; "2"; "3"} lists
-- - etc.
parseContainer :: Text -> Text -> Text -> Parser a -> Parser [a]
parseContainer beg end sep item = do
  _ <- parseTerminal beg
  items <- sepBy item $ parseTerminal sep
  _ <- parseTerminal end
  return items

-- | Parse a couple (a, b)
-- Format is (a, b).
parseCouple :: Parser a -> Parser b -> Parser (a, b)
parseCouple parserA parserB = do
  _ <- parseTerminal "("
  a <- parserA
  _ <- parseTerminal ","
  b <- parserB
  _ <- parseTerminal ")"
  return (a, b)

-- | Parse a list [a]
-- Format is [a1, a2, ...] where as are identifiers.
parseList :: Parser a -> Parser [a]
parseList = parseContainer "[" "]" ","

-- | Parse a terminal.
parseTerminal :: Text -> Parser ()
parseTerminal sep = do
  _ <- many space
  _ <- string sep
  return ()

-- | Parse an identifier
parseIdentifier :: Parser Id
parseIdentifier = do
  _ <- many space
  car1 <- satisfy (inClass "A-Za-z_")
  rest <- A.takeWhile (inClass "A-Za-z0-9_")
  return $ [car1] <> toString rest

-- |  Parse a string.
parseString :: Parser String
parseString = many space *> "\"" *> manyTill anyChar "\""

-- | Parse an integer.
parseInteger :: Parser Integer
parseInteger = many space *> decimal

-- | Converts a maybe into an either using a possible error message.
validate :: a -> Maybe b -> Either a b
validate errorMessage m = case m of
            Nothing -> Left errorMessage
            Just v  -> Right v

-- | Converts a maybe into an either using a possible error message.
-- Practical to be used in infix form.
(?#) :: Maybe a -> Text -> TEither a
(?#) = flip validate

-- | Transforms a list into an either with a message error if the list is empty.
listToEither :: Text -> [a] -> TEither [a]
listToEither errorMessage xs = if null xs then Left errorMessage else Right xs

-- | Fixpoint computation for Sets.
setFixpoint :: (Eq a) => (Set a -> Set a) -> Set a -> Set a
setFixpoint f s
  | s == s' = s
  | otherwise = f s'
  where
    s' = f s

-- |
-- Fixpoint computation for Lists (based on sets).
-- Stops upon set equality, i.e. will stop if @f [1,2] = [2,1]@
listFixpoint :: (Ord a) => ([a] -> [a]) -> [a] -> [a]
listFixpoint f xs
  | S.fromList xs == S.fromList xs' = xs
  | otherwise = listFixpoint f xs'
  where
    xs' = (toList . S.fromList) $ f xs
