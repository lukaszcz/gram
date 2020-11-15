module Utils where

group :: [Int] -> [a] -> [[a]]
group (n:ns) xs = l : group ns xs'
    where (l, xs') = splitAt n xs
group [] xs = [xs]
