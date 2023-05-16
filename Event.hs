module Event (makeEvent) where

import Define (State(..),Play(..),Mode(..))
import Grid(changeGridType,intoGrid,clFromGrid)
import Libs(sepByChar,getIndex,concatWith)

makeEvent :: String -> State -> State
makeEvent scr st = 
  let (f:es) = sepByChar '.' scr
   in case f of
        "e" -> addEvent es st
        "d" -> delEvent es st
        "da" -> delAllEvent st
        "ct" -> changeType es st 
        "p" -> putCell es st
        "cleq" -> clearEqual st
        "m" -> addMemory es st
        "if" -> makeDecision es st
        "ch" -> makeChoice es st
        _   -> st

clearEqual :: State -> State 
clearEqual st = let p = player st
                 in st{player=p{gr=clFromGrid '=' (gr p)}} 

putCell :: [String] -> State -> State 
putCell [] st = st 
putCell (a:b:xs) st = let p = player st
                          (x':y':_) = sepByChar ',' a
                          (chs:tps:_) = sepByChar ',' b
                          x = read x'::Int; y = read y'::Int
                          ch = head chs; tp = readType tps
                       in putCell xs st{player=p{gr=intoGrid (x,y) (ch,tp) (gr p)}}

readType :: String -> Mode
readType str = case str of "Fr"->Fr; "Bl"->Bl; "Ex"->Ex; "Mv"->Mv; "Pn"->Pn; "Wn"->Wn; "Cm"->Cm; "DB"->DB; "DF"->DF;

changeType :: [String] -> State -> State 
changeType [] st = st 
changeType (a:b:xs) st = let p = player st
                             tp = readType b
                          in changeType xs st{player=p{gr=changeGridType (head a,tp) (gr p)}}

addEvent :: [String] -> State -> State
addEvent [] st = st
addEvent (a:b:xs) st = addEvent xs st{evt=(a,b):evt st,ecs=0:ecs st}

delAllEvent :: State -> State
delAllEvent st = st{evt=[]}

delEvent :: [String] -> State -> State
delEvent [] st = st
delEvent (x:xs) st = let evs = evt st
                         cs = ecs st
                         evks = map fst evs
                         idel = elem x evks
                         ind = if idel then getIndex x evks else (-1)
                         nevt = if idel then delFrom ind evs else evs
                         necs = if idel then delFrom ind cs else cs
                      in delEvent xs st{evt=nevt,ecs=necs}

delFrom :: Int -> [a] -> [a]
delFrom id lst = take id lst ++ drop (id+1) lst

addMemory :: [String] -> State -> State
addMemory [] st = st
addMemory (k:v:xs) st = addMemory xs st{mem=(k,v):mem st}

makeDecision :: [String] -> State -> State
makeDecision [] st = st
makeDecision (m:c:xs) st
  | m `elem` ks = if c==vs!!getIndex m ks then makeEvent ts st else fsst
  | otherwise = fsst
  where (ks,vs) = unzip (mem st)
        (ts:fs) = sepByChar '/' (concatWith '.' xs)
        fsst = if null fs then st else makeEvent (head fs) st

makeChoice :: [String] -> State -> State
makeChoice [] st = st{ich=True,imp=True}
makeChoice (x:xs) st = let (c:d:_) = sepByChar ',' x 
                        in makeChoice xs st{chd=chd st++[(c,d)]}

--------------------------------------------------------------------
