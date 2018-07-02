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

info :: String -> IO (Int , Int)
info f =
  do xs <- readFile f
     return ((length . lines) xs),
             (count (prefix begin) (prefix end) . lines) xs)

pad :: Int -> String -> String
pad n s  =  take n (s ++ repeat ' ')

rjust :: Int -> String -> String
rjust n = reverse . pad n . reverse

format :: String -> IO String
format "--" = ""
format f =
  do (lines, code) <- info f
     return (replicate 4 ' ' ++
             pad 28 f ++
             rjust 4 lines ++
             replicate 4 ' ' ++
             rjust 4 ' ')

config : IO [String]
config =
  do stuff <- readFile "config.txt"
     return (lines stuff)

answer : IO String
answer =
  do 