module OutToCanvas where

import Haste.Graphics.Canvas(Canvas,Color(RGB),color,font,translate,rotate,
                             text,render,renderOnTop)
import Haste.DOM (fromElem,elemById)
import Control.Monad (when)
import Define (iy,imx,igx,wg,hg,wt,ht,cvH,cvT,nfs,rfs,State(..),Play(..),Grid,Pos,Mode(..),Msg,Fsize)
import Browser 
import Event(makeEvent)
import Libs(getInside)

putMessageG :: Canvas -> State -> IO State
putMessageG c st = do
    if ims st && not (imp st) then do
          let ms = msg st
              mc = mct st
              ml = length ms-1 
              (_,h) = sz st
              iq = iy+h+3
              (p,q) = if mc==0 then (imx,iq) else mps st
              tmsg = take (mc+1) ms 
              lmsg = last tmsg
              ch = case lmsg of '、' -> ' '; '。' -> ' '; '}' -> ' ';  _ -> lmsg 
              ic = ch=='「'
              ir = ch=='\n'
              ip = lmsg=='。'
              irb = ch=='：'
              isc = ch=='{'
              cln
                |ir = 0
                |ic = 1
                |otherwise = mcl st
              col = chColors!!cln
              rbs = if irb then getInside '：' mc ms else ""
              scr = if isc then getInside '}' mc ms else ""
              cta
                |irb = length rbs + 2
                |isc = length scr + 2
                |otherwise = 1
              nmct = if mc+cta>ml then 0 else mc+cta
              nims = mc+cta <= ml
              npos
                |irb = (p,q)
                |ir = (p-1,iq)
                |otherwise = nextPQ iq (p,q) 
              iscx = fst npos==1 && fst npos/=p
              nst = if isc then makeEvent scr st{imp=ip} else st{imp=ip}
              scx = if mc==0 then 0 else msc nst
              npos' = if iscx then (p,iq) else npos
              nmsc = if iscx then scx+1 else scx
              eq = floor ((cvH-cvT)/ht)
              p' = if iq==q then p+1 else p
              q' = if iq==q then eq else q-1
          if irb then mapM_ (\(ch,rd) -> putLet c col rfs rd (p',q') ch) (zip rbs [0,1..]) 
                 else if isc then when (ich nst) $ do
                                      let (dlgs,_) = unzip (chd nst)
                                          cmsg = makeChoiceMessage (msg nst) dlgs (chn nst) 
                                      clearMessage c nst
                                      putMessageT c (imx+scx,iq) cmsg
                             else if iscx then do 
                                      clearMessage c nst
                                      putMessageT c (imx+scx+1,iq) (take (mc+1) ms)
                                          else putLet c col nfs 0 (p,q) ch 
          return nst{ims=nims,mct=nmct,mps=npos',mcl=cln,msc=nmsc}
                else return st

addRubi :: Int -> String -> String
addRubi _ [] = []
addRubi mc msg
  | msg!!mc=='：' = take (mc+1) msg
  | otherwise = addRubi (mc+1) msg

makeChoiceMessage :: Msg -> [String] -> Int -> Msg 
makeChoiceMessage omsg dlgs cn = let ndlgs = makeDialogs dlgs cn
                                  in omsg ++ "\n\n" ++ concatMap (++"\n\n") ndlgs

makeDialogs :: [String] -> Int -> [String]
makeDialogs dlgs cn = makeDialogs' dlgs cn 0
  where makeDialogs' [] _ _ = []
        makeDialogs' (x:xs) cn i 
          |cn==i =  if head x=='*' then (' ':x):nmd else ('*':x):nmd
          |head x=='*' = (' ':tail x):nmd
          |otherwise = (' ':x):nmd
                       where nmd = makeDialogs' xs cn (i+1)

putMessage :: Canvas -> Pos -> Msg -> IO ()
putMessage _ _ [] = return ()
putMessage c (p,q) msg = putMozi c (head chColors) (p,q) msg 

putMessageT :: Canvas -> Pos -> String -> IO ()
putMessageT c (p,q) = putLetters c 0 q (p,q) 

putLetters :: Canvas -> Int -> Int -> Pos -> String -> IO ()
putLetters _ _ _ _ [] = return ()
putLetters c cln iq (p,q) (x:xs) = do
  case x of 
    '{'   -> putNothing c cln iq (p,q) xs
    '：'  -> putRubi c cln iq (if iq==q then p+1 else p,if iq==q then eq else q-1) xs
                where eq = floor ((cvH-cvT)/ht)
    '\n'  -> putLetters c 0 iq (p-1,iq) xs
    _     -> do let lt = case x of '、' -> '@'; '。' -> '@'; '*' -> '@';  _ -> x
                    ncln = case x of
                             '「' -> 1
                             '*'  -> 3
                             _    -> cln
                    col = chColors!!ncln
                when (lt/='@') $ putLet c col nfs 0 (p,q) lt 
                let (p',q') = nextPQ iq (p,q)
                putLetters c ncln iq (p',q') xs

putNothing :: Canvas -> Int -> Int -> Pos -> String -> IO ()
putNothing _ _ _ _ [] = return ()
putNothing c cln iq (p,q) (x:xs) = do
  case x of
    '}' -> do let (p',q') = nextPQ iq (p,q)
              putLetters c cln iq (p',q') xs
    _   -> putNothing c cln iq (p,q) xs

nextPQ :: Int -> Pos -> Pos
nextPQ iq (p,q)
  | (fromIntegral q+1)*ht > cvH - cvT = (p-1,iq)
  | otherwise = (p,q+1)

putRubi :: Canvas -> Int -> Int -> Pos -> String -> IO ()
putRubi c cln iq (p,q) = pRubi c iq 0 (p,q)
  where
    col = chColors!!cln
    pRubi _ _ _ _ [] = return ()
    pRubi c iq rd (p,q) (x:xs) = do
      case x of
        '：' -> let (p',q')=nextPQ iq (p,q)
                 in putLetters c cln iq (p',q') xs
        _    -> do putLet c col rfs rd (p,q) x 
                   pRubi c iq (rd+1) (p,q) xs

putGrid :: Canvas -> Pos -> Grid -> IO ()
putGrid c (x,y) grid = do 
  putMoziCl c
  putMozi c (head chColors) (x,y) edgeLine
  putInside (x,y+1) grid
    where gridWidth = length (head grid)
          edgeLine = "-"++replicate gridWidth '-'++"-"
          putInside (p,q) [] = putMozi c (head chColors) (p,q) edgeLine
          putInside (p,q) (g:gs) = do
            let inside = map (\(ch,tp) -> if tp==DB || tp==DF then ' ' else ch) g
            putMozi c (head chColors) (p,q) ("|"++inside++"|")
            putInside (p,q+1) gs

putMoziCl :: Canvas -> IO ()
putMoziCl c = do
  render c $ text (0,0) "" 

clearMessage :: Canvas -> State -> IO ()
clearMessage c st = do
  putMoziCl c
  let p = player st 
      (wd,_) = sz st
      (x,y) = xy p 
      pxy = (x+1+igx-wd,y+iy+1)
      cnm = if et p==' ' then 1 else 2
  putGrid c (igx-wd,iy) (gr p)
  putMozi c (chColors!!cnm) pxy [pl p]


putMozi :: Canvas -> Color -> Pos -> String -> IO ()
putMozi c col (x,y) str = do
  let (px,py) = (fromIntegral x,fromIntegral y)
  renderOnTop c $ do
    mapM_ (\(ch,n)->color col$font (show nfs++"px Unifont")$
      text (px*wg+wg*n,py*hg) [ch]) (zip str [0..]) 

putLet :: Canvas -> Color -> Fsize -> Double -> Pos -> Char -> IO ()
putLet c col fs rd (x,y) ch = do
  renderOnTop c $ color col$font (show fs++"px VL Gothic")$
    translate (px+ex,py-ext)$rotate rta$text (0,0) [ch]
      where irt = rtChar ch
            (p,q) = (fromIntegral x,fromIntegral y)
            fsd = fromIntegral fs
            nfsd = fromIntegral nfs
            rfsd = fromIntegral rfs
            (px,py) = if fs==rfs then (p*wt+nfsd,q*ht+rfsd*(rd-1))
                                  else (p*wt,q*ht)
            rta = if irt then pi/2 else 0
            ex = if irt then nfsd/6 else 0
            ext = if irt then nfsd/6*5 else 0
            
rtChar :: Char -> Bool
rtChar ch = (cp>31 && cp<128)||(ch `elem` "ー〜。「＜＞") 
  where cp = fromEnum ch
