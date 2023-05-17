module CvLoop (initiate,inputLoop,mouseClick) where

import Haste.Graphics.Canvas(Canvas)
import Haste.Audio
import Control.Monad(unless)
import Define
import Stages(stages,players,initPos,gridSize,idef,evts)
import FiFunc(funcPon,stagePon,doNothing)
import Grid
import Messages
import Browser 
import OutToCanvas
import Check(checkDef,checkEq,checkEv,getMessage)
import Siki
import Libs(getIndex,getRandomNumIO,getRandomNum)

initState :: State
initState = State {player=initPlayer,sz=igs,msg=initMsg,evt=evts,
                   ecs=replicate (length evts) 0,mem=[],
                   mps=(0,0),mct=0,mcl=0,msc=0,jps= -1,chd=[],chn=0,
                   ils=False,igc=False,ims=True,imp=False,itc=False,ini=False,
                   ich=False,db="",ch=' '}
                     where igs = head gridSize

initPlayer :: Play
initPlayer = Play {xy=head initPos,gr=makeGrid igs (head stages),pl=head players,et=' ',
                   sn=0,rgn=0,elg="",iw=False,isc=False}
                     where igs = head gridSize

keyCheck :: Size -> Pos -> Char -> Pos 
keyCheck (wd,hi) (x,y) ch  
  | ch=='j'||ch=='P' = if hi==y+1 then (x,y) else (x,y+1)
  | ch=='k'||ch=='H' = if 0>y-1 then (x,y) else (x,y-1)
  | ch=='h'||ch=='K' = if 0>x-1 then (x,y) else (x-1,y)
  | ch=='l'||ch=='M' = if wd==x+1 then (x,y) else (x+1,y)
  | otherwise = (x,y) 

keyChoice :: Int -> Int -> Char -> Int
keyChoice mx cn ch
  | ch=='j'||ch=='P'||ch=='h'||ch=='K' = if cn==mx then 0 else cn+1
  | ch=='k'||ch=='H'||ch=='l'||ch=='M' = if cn==0 then mx else cn-1
  | ch==' ' = -1
  | otherwise = -2

fpon :: Char -> Char -> Char
fpon p e = let (cs,fs)=unzip funcPon 
               f = fs!!getIndex p cs
            in f e

spon :: Int -> Char -> Char -> Char
spon i e t = let (sn,fs)=unzip stagePon
                 f = if i `elem` sn then fs!!getIndex i sn else doNothing
              in f e t

putOut :: Play -> Play 
putOut p =
  let (Play pos grid pla eat snum _ lg _ _) = p
      (ch,tp) = fromGrid pos grid 
      iout = eat/=' ' && ch==' '
      ipn = tp==Pn
      eat' = if iout then ' ' else eat
      ch' = let fch = fpon pla eat in if iout then fch else 
                                        if ipn then spon snum fch ch else ch
      grid' = intoGrid pos (ch',tp) grid 
      def = checkDef snum idef grid'
      (isc',_) = checkEq def grid'
      lg' 
        | isc' = "==" 
        | iout = 'o':[ch'] 
        | ipn = 'p':[ch']
        | otherwise = ""
   in p{gr=grid',et=eat',isc=isc',elg=lg++lg'}

plMove :: Pos -> Play -> Play 
plMove (x,y) p = 
  let (Play mpos grid pla eat snum gen lg iwn is) = p
      (ch,tp) = fromGrid (x,y) grid 
      fps = map fst funcPon
      ifp = eat==' ' && ch `elem` fps && tp==Fr
      ieat = eat==' ' && ch/=' ' && (tp==Fr||tp==DF) && not ifp
      ibum = (tp==Bl||tp==DB||tp==Wn)
      iex = tp==Ex
      eat' = if ieat then ch else eat
      pla' = if ifp then ch else pla 
      ch' 
        |ieat = ' '
        |ifp = pla
        |otherwise = ch
      grid' = intoGrid (x,y) (ch',tp) grid
      imv = tp==Mv || (tp==Pn && eat==' ')
      grid'' = if imv then obMove mpos (x,y) grid' else grid'
      ngrid = if iwn then wnMove gen (x,y) grid'' else grid''
      (x',y')=if (imv&&ngrid==grid')||ibum then mpos else (x,y)
      (isc',lf) = if imv then checkEq (checkDef snum idef ngrid) ngrid else (is,"")
      lg' 
        | ieat = 'e':[ch]
        | ifp = 'f':[ch] 
        | imv&&isc' = "==" 
        | imv&&mpos/=(x',y') = 'v':[ch]
        | tp==Pn = 'n':[ch] 
        | ibum = if ch=='=' then 'b':(ch:show y) else 'b':[ch]
        | iex = 'u':[ch] 
        | otherwise = ""
   in p{xy=(x',y'),gr=ngrid,pl=pla',et=eat',isc=isc',elg=lg++lg'} 

mkDir :: Pos -> Pos -> Dir
mkDir (x0,y0) (x1,y1)
  |x1>x0 = Rt
  |x0>x1 = Lf
  |y1>y0 = Dw
  |y0>y1 = Up
  |otherwise = Cn

obMove :: Pos -> Pos -> Grid -> Grid
obMove mpos (x,y) grid =
  let gline = grid!!y
      (ch,tp) = gline!!x 
      ngrid = intoGrid (x,y) (' ',Fr) grid 
      dir = mkDir mpos (x,y)
      (x',y') = case dir of
                  Up -> if y==0 then (-1,-1) else (x,y-1)
                  Dw -> if y==length grid-1 then (-1,-1) else (x,y+1)
                  Lf -> if x==0 then (-1,-1) else (x-1,y)
                  Rt -> if x==length gline-1 then (-1,-1) else (x+1,y)
      tgline = if y'==(-1) then [] else ngrid!!y'
      (tch,_) = if x'==(-1) then (' ',Fr) else tgline!!x'
      imv = x'/=(-1) && tch==' '
      ngline' = take x' tgline++[(ch,tp)]++drop (x'+1) tgline
   in if imv then take y' ngrid ++[ngline']++ drop (y'+1) ngrid
             else grid

wnMove :: Int -> Pos -> Grid -> Grid
wnMove gen pos grid = wnMove' gen (0,0) grid pos grid
  where (sx,sy) = sizeGrid grid 
        wnMove' _ _ ngrid _ [] = ngrid
        wnMove' g (x,y) ngrid pos (((ch,tp):xs):ys)
          | tp==Wn = 
              let (n,g') = getRandomNum (5,g) 
                  (x',y') = case n of
                              0->(x,y); 1->(x-1,y); 2->(x,y-1); 3->(x+1,y); 4->(x,y+1)
                              _->(x,y)
                  imv = (x'>=0 && x'<sx && y'>=0 && y'<sy && (x',y')/=pos)
                  ch' = if imv then fst$fromGrid (x',y') ngrid else 'x'
                  (nx,ny) = if ch'==' ' && imv then (x',y') else (x,y)
                  ngrid' = if (nx,ny)==(x,y) 
                      then ngrid else intoGrid (x,y) (' ',Fr) (intoGrid (nx,ny) (ch,tp) ngrid)
               in if null xs then wnMove' g' (0,y+1) ngrid' pos ys
                             else wnMove' g' (x+1,y) ngrid' pos (xs:ys)
          | otherwise = if null xs then wnMove' g (0,y+1) ngrid pos ys
                                   else wnMove' g (x+1,y) ngrid pos (xs:ys)

initiate :: Canvas -> IO State 
initiate c = do
  let (x,y)=(xy.player) initState
      (wd,hi)=sz initState
      (px,py)=(x+1,y+iy)
  putGrid c (igx-wd,iy) ((gr.player) initState)
  putMozi c (chColors!!1) (px+igx-wd,py+1) "@"
  return initState 

keyCodeToChar :: Int -> Char
keyCodeToChar kc = case kc of
                     72 -> 'h';74 -> 'j';75 -> 'k';76 -> 'l';78 -> 'n';
                     _  -> toEnum kc

mouseClick :: Canvas -> Double -> Double -> State -> IO State
mouseClick c p q = inputLoop c (flToKc (clFields p q fields)) 

skipMessage :: Canvas -> State -> IO State
skipMessage c st = do
  st' <- putMessageG c st
  if imp st' || not (ims st) then return st'{ini=False}
                             else skipMessage c st'

inputLoop :: Canvas -> Int -> State -> IO State 
inputLoop c kc st = do
  if ini st then return st else
    if ims st && not (imp st) then skipMessage c st{ini=True} else
      if imp st then do
        if ich st then do
          print "choice"
          let i = keyCodeToChar kc
              (wd,hi) = sz st
              (dlgs,mnas) = unzip (chd st)
              cn = chn st
              ncn = keyChoice (length dlgs - 1) cn i
          if ncn == (-1) then do 
                              let nmsg = getMessage (mnas!!cn)
                              clearMessage c st
                              return st{msg=nmsg,ims=True,ich=False, imp=False}
                         else
            if ncn == (-2) then return st
                           else do
                               let cmsg = makeChoiceMessage (msg st) dlgs ncn 
                               clearMessage c st
                               putMessageT c (imx+ msc st,iy+hi+3) cmsg
                               return st{chn=ncn}
                    else return st{imp=False}
                  else do
      let p = player st
      print (evt st)
      print (ecs st)
      print (mem st)
      print (elg p)
      print (isc p)
      print (ich st)
      print (jps st)
      (_,nrg) <- getRandomNumIO (5,rgn p)
      let i = keyCodeToChar kc 
          (x,y) = xy p 
          (wd,hi) = sz st
          (x',y') = keyCheck (wd,hi) (x,y) i
          p' = plMove (x',y') p
          (tx,ty) = xy p'
          (px,py) = (x+1,y+iy)
          (px',py') = (tx+1,ty+iy)
          p'' = if i==' ' then putOut p' else p'
          nst = checkEv 0 (elg p'') (evt st) st{player=p''{rgn=nrg}}
          (wd',_) = sz nst
      putGrid c (igx-wd',iy) (gr (player nst))
      unless (ims nst) $ putMessageT c (imx+msc nst,iy+hi+3) (msg nst)
      if ils nst || i=='n' then nextStage c nst{ims=False} 
                           else do
         let pxy = (px'+igx-wd,py'+1)
         if et (player nst)==' ' then putMozi c (chColors!!1) pxy [pl p'']
                        else putMozi c (chColors!!2) pxy [pl p'']
         return nst

showLog :: Canvas -> String -> IO ()
showLog c log = do
   let els = divStr 25 log 
       divStr i str
         | length str<=i = [str]
         | otherwise = take i str:divStr i (drop i str)
   mapM_ (\(el,i) -> putMozi c (chColors!!1) (1,30+i) el) (zip els [0,1..])

nextStage :: Canvas -> State -> IO State 
nextStage c st = do
  let p = player st
      js = jps st
      nsn = if js<0 then sn p + 1 else js
      maxSn = length stages
      gc = nsn == maxSn
      nlg = elg p++'c':show (sn p)
  if gc then gameClear c st
        else do
          let nsz=gridSize!!nsn
              grid=makeGrid nsz (stages!!nsn)
              iwn=checkGrid (' ',Wn) grid
              np = p{xy=initPos!!nsn, gr=grid, pl=players!!nsn, et=' ',sn=nsn,
                     elg=nlg,isc=False,iw=iwn}
          inputLoop c 64 st{sz=nsz,player=np,msg="",jps = -1,ils=False,igc=False}

gameClear :: Canvas -> State -> IO State 
gameClear c st = do putMoziCl c
                    let col=head chColors
                    putMozi c col (2,5) "Congratulations!"
                    putMozi c col (3,8) "Coding : yokoP"
                    putMozi c col (3,10) "Test Play : takaPon"
                    putMozi c col (4,14) "I spent a special week"
                    putMozi c col (5,15) "10/18 to 10/25 in 2021"
                    putMozi c col (2,17) "Thank you for playing!"
                    let nsz=head gridSize
                        p = player st
                        np=p{xy = head initPos, gr=makeGrid nsz (head stages),
                             pl=head players,et=' ',sn=0,elg="",isc=False}
                    return st{sz=nsz,player=np,igc=False}
