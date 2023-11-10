module OutToCanvas(putMessageG,putMessageT,putGrid,putMoziCl
                  ,clearMessage,putMozi,putWst) where

import Haste.Graphics.Canvas(Canvas,Color(RGB),Bitmap,color,font,translate,rotate
                            ,text,draw,scale,render,renderOnTop)
import Haste.DOM (fromElem,elemById)
import Control.Monad (when)
import Define (iy,wg,hg,wt,ht,cvT,nfs,rfs,State(..),Play(..),Switch(..),CInfo,Grid,Pos
              ,Mode(..),Msg,Fsize,wstIndex)
import Browser(chColors)
import Event(makeEvent)
import Action(makeChoiceMessage)
import Libs(getInside, getIndex)
  {--
putMessageG :: Canvas -> CInfo -> State -> IO State
putMessageG c ((cvW,cvH),_) st = do
    let sw = swc st
    if ims sw && not (imp sw) then do
          let ms = msg st
              mc = mct st
              ml = length ms-1 
              h = if ism sw then snd (sz st) + 3 else 0
              imx = floor (cvW/wt) - 1
              igx = floor (cvW/wg) - 2
              iq = iy+h
              (p,q) = if mc==0 then (imx,iq) else mps st
              tmsg = take (mc+1) ms 
              lmsg = if null tmsg then ' ' else last tmsg
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
                |otherwise = nextPQ cvH iq (p,q) 
              iscx = fst npos==1 && fst npos/=p
              nst = if isc then makeEvent scr st{swc=sw{imp=ip}} else st{swc=sw{imp=ip}}
              nsw = swc nst
              scx = if mc==0 then 0 else msc nst
              npos' = if iscx then (p,iq) else npos
              nmsc = if iscx then scx+1 else scx
              eq = floor ((cvH-cvT)/ht)
              p' = if iq==q then p+1 else p
              q' = if iq==q then eq else q-1
          if irb then mapM_ (\(ch,rd) -> putLet c col rfs rd (p',q') ch) (zip rbs [0,1..]) 
                 else do
                   let itp0 = isc && ich nsw
                       itp1 = not isc && iscx
                       msg'
                        | itp0 = let (dlgs,_) = unzip (chd nst)
                                  in makeChoiceMessage (msg nst) dlgs (chn nst) 
                        | itp1 = take (mc+1) ms
                        | otherwise = ""
                       posx
                        | itp0 = imx+scx
                        | itp1 = imx+scx+1
                        | otherwise = 0
                   when (itp0||itp1) $ clearMessage c igx nst >> putMessageT c cvH (posx,iq) msg'
                   when (not isc && not iscx) $ putLet c col nfs 0 (p,q) ch
          return nst{mct=nmct,mps=npos',mcl=cln,msc=nmsc,swc=nsw{ims=nims}}
    else return st
    --}

prepareMessage (cvW,cvH) sw st =
  let ms = msg st
      mc = mct st
      ml = length ms-1 
      h = if ism sw then snd (sz st) + 3 else 0
      imx = floor (cvW/wt) - 1
      igx = floor (cvW/wg) - 2
      iq = iy+h
      (p,q) = if mc==0 then (imx,iq) else mps st
      tmsg = take (mc+1) ms 
      lmsg = if null tmsg then ' ' else last tmsg
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
        |otherwise = nextPQ cvH iq (p,q) 
      iscx = fst npos==1 && fst npos/=p
      nst = if isc then makeEvent scr st{swc=sw{imp=ip}} else st{swc=sw{imp=ip}}
      nsw = swc nst
      scx = if mc==0 then 0 else msc nst
      npos' = if iscx then (p,iq) else npos
      nmsc = if iscx then scx+1 else scx
      eq = floor ((cvH-cvT)/ht)
      p' = if iq==q then p+1 else p
      q' = if iq==q then eq else q-1
   in (ch,p,q,p',q',iq,mc,ms,col,rbs,imx,igx,scx,rfs,irb,isc,iscx,nmct,npos',cln,nmsc,nims,nsw,nst) 

prepareNormal isc iscx mc ms imx scx nsw nst =
    let itp0 = isc && ich nsw
        itp1 = not isc && iscx
        msg'
          | itp0 = let (dlgs,_) = unzip (chd nst)
                    in makeChoiceMessage (msg nst) dlgs (chn nst) 
          | itp1 = take (mc+1) ms
          | otherwise = ""
        posx
          | itp0 = imx+scx
          | itp1 = imx+scx+1
          | otherwise = 0
     in (itp0, itp1, msg', posx) 

putMessageG :: Canvas -> CInfo -> State -> IO State
putMessageG c ((cvW,cvH),_) st = do 
   let sw = swc st
   if ims sw && not (imp sw) then do
     let (ch,p,q,p',q',iq,mc,ms,col,rbs,imx,igx,scx,rfs,irb,isc,iscx,nmct,npos',cln,nmsc,nims,nsw,nst)
            = prepareMessage (cvW,cvH) sw st
     if irb then mapM_ (\(ch,rd) -> putLet c col rfs rd (p',q') ch) (zip rbs [0,1..]) 
            else do
              let (itp0,itp1,msg',posx) = prepareNormal isc iscx mc ms imx scx nsw nst
              when (itp0||itp1) $ clearMessage c igx nst >> putMessageT c cvH (posx,iq) msg'
              when (not isc && not iscx) $ putLet c col nfs 0 (p,q) ch
     return nst{mct=nmct,mps=npos',mcl=cln,msc=nmsc,swc=nsw{ims=nims}}
   else return st

putMessageT :: Canvas -> Double -> Pos -> String -> IO ()
putMessageT c cvH (p,q) = putLetters c cvH 0 q (p,q) 

putLetters :: Canvas -> Double -> Int -> Int -> Pos -> String -> IO ()
putLetters _ _ _ _ _ [] = return ()
putLetters c cvH cln iq (p,q) (x:xs) = do
  case x of 
    '{'   -> putNothing c cvH cln iq (p,q) xs
    '：'  -> putRubi c cvH cln iq (if iq==q then p+1 else p,if iq==q then eq else q-1) xs
                where eq = floor ((cvH-cvT)/ht)
    '\n'  -> putLetters c cvH 0 iq (p-1,iq) xs
    _     -> do let lt = case x of '、' -> '@'; '。' -> '@'; '*' -> '@';  _ -> x
                    ncln = case x of
                             '「' -> 1
                             '*'  -> 2
                             _    -> cln
                    col = chColors!!ncln
                when (lt/='@') $ putLet c col nfs 0 (p,q) lt 
                let (p',q') = nextPQ cvH iq (p,q)
                putLetters c cvH ncln iq (p',q') xs

putNothing :: Canvas -> Double -> Int -> Int -> Pos -> String -> IO ()
putNothing _ _ _ _ _ [] = return ()
putNothing c cvH cln iq (p,q) (x:xs) = do
  case x of
    '}' -> do let (p',q') = nextPQ cvH iq (p,q)
              putLetters c cvH cln iq (p',q') xs
    _   -> putNothing c cvH cln iq (p,q) xs

nextPQ :: Double -> Int -> Pos -> Pos
nextPQ cvH iq (p,q)
  | (fromIntegral q+1)*ht > cvH - cvT = (p-1,iq)
  | otherwise = (p,q+1)

putRubi :: Canvas -> Double -> Int -> Int -> Pos -> String -> IO ()
putRubi c cvH cln iq (p,q) = pRubi c iq 0 (p,q)
  where
    col = chColors!!cln
    pRubi _ _ _ _ [] = return ()
    pRubi c iq rd (p,q) (x:xs) = do
      case x of
        '：' -> let (p',q')=nextPQ cvH iq (p,q)
                 in putLetters c cvH cln iq (p',q') xs
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

clearMessage :: Canvas -> Int -> State -> IO ()
clearMessage c igx st = do
  putMoziCl c
  let isMap = ism$swc st 
  when isMap $ do
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
    mapM_ (\(ch,n)->color col$font (show nfs++"px Courier")$
      text (px*wg+wg*n,py*hg) [ch]) (zip str [0..]) 

putLet :: Canvas -> Color -> Fsize -> Double -> Pos -> Char -> IO ()
putLet c col fs rd (x,y) ch = do
  renderOnTop c $ color col$font (show fs++"px IPAGothic")$
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

putWst :: Canvas -> [Bitmap] -> Fsize -> Pos -> Char -> IO () 
putWst c wsts fs (x,y) ch = do
  renderOnTop c $ translate (px, py+5) $ scale (0.7,0.7) $ draw (wsts!!ind) (0,0)
    where ind = if ch `elem` wstIndex then getIndex ch wstIndex else 14
          (px,py) = (fromIntegral x * wg, fromIntegral y * hg)
            
rtChar :: Char -> Bool
rtChar ch = (cp>31 && cp<128)||(ch `elem` "ー〜。「＜＞（）") 
  where cp = fromEnum ch
