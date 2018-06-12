import Prelude

begin :: String
begin =  "\\begin{code}"

end :: String
end =  "\\end{code}"

prefix :: Eq a => [a] -> [a] -> Bool
prefix xs ys  =  take (length xs) ys == xs

test0 :: Bool
test0 =  prefix "abc" "abcde" &&
         prefix "abc" "abc"   &&
         not (prefix "abc" "ab")

strip :: (a -> Bool) -> (a -> Bool) -> [a] -> [[a]]
strip b e []  =  []
strip b e xs  =
  let  us = (drop 1 . dropWhile (not . b)) xs  in
  let  vs = takeWhile (not . e) us  in
  let  ws = (drop 1 . dropWhile (not . e)) us  in
  vs : strip b e ws

ex1 = "xbyexxbyyexxxbyyyexxxx"

test1 :: Bool
test1 =  strip (== 'b') (== 'e') ex1 == ["y","yy","yyy",""]

count :: (a -> Bool) -> (a -> Bool) -> [a] -> Int
count b e = sum . map length . strip b e

test2 :: Bool
test2 =  count (== 'b') (== 'e') ex1 == 6

agda :: String -> IO Int
agda f =
  do xs <- readFile f
     return ((count (prefix begin) (prefix end) . lines) xs)
     