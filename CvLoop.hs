module CvLoop (initiate,inputLoop,mouseClick) where

import Haste.Graphics.Canvas(Canvas)
import Haste.Audio
import Control.Monad(unless)
import Define(State(..),Play(..),Mode(..),CInfo,iy,wg,wt)
import Stages(stages,players,initPos,gridSize)
import Grid(checkGrid,makeGrid)
import Browser(chColors,clFields,flToKc,fields,cvRatio)
import OutToCanvas(putMessageG,putMessageT,putGrid,putMoziCl,clearMessage,putMozi)
import Check(checkEv,getMessage)
import Libs(getRandomNumIO)
import Action(initState,keyCodeToChar,keyChoice,keyCheck,putOut,plMove,makeChoiceMessage)

initiate :: Canvas -> CInfo -> IO State 
initiate c ((cvW,_),_) = do
  let (x,y)=(xy.player) initState
      (wd,hi)=sz initState
      (px,py)=(x+1,y+iy+1)
      igx = floor (cvW/wg) - 2
      ix = igx-wd
  putGrid c (ix,iy) ((gr.player) initState)
  putMozi c (chColors!!1) (px+ix,py) "@"
  return initState 

mouseClick :: Canvas -> CInfo -> Int -> Int -> State -> IO State
mouseClick c ci x y = do
  let (rtx,rty) = cvRatio ci
      nx = fromIntegral x*rtx
      ny = fromIntegral y*rty
      cvWH = fst ci
  inputLoop c ci (flToKc (clFields nx ny (fields cvWH))) 

skipMessage :: Canvas -> CInfo -> State -> IO State
skipMessage c ci st = do
  st' <- putMessageG c ci st
  if imp st' || not (ims st) then return st'{ini=False}
                             else skipMessage c ci st'

inputLoop :: Canvas -> CInfo -> Int -> State -> IO State 
inputLoop c ci@((cvW,cvH),_) kc st
  | iniSt = return st
  | imsSt && not impSt = skipMessage c ci st{ini=True} 
  | impSt = do 
      if ichSt then do
          print "choice"
          let i = keyCodeToChar kc
              (wd,hi) = szSt
              (dlgs,mnas) = unzip (chd st)
              cn = chn st
              ncn = keyChoice (length dlgs - 1) cn i
          case ncn of
            (-1) -> do 
                      let nmsg = getMessage (mnas!!cn)
                      clearMessage c igx st
                      return st{msg=nmsg,ims=True,ich=False, imp=False}
            (-2) -> return st
            _    -> do
                      let cmsg = makeChoiceMessage (msg st) dlgs ncn 
                      clearMessage c igx st
                      putMessageT c cvH (imx+ msc st,iy+hi+3) cmsg
                      return st{chn=ncn}
                else return st{imp=False}
  |otherwise = do
      let p@(Play xyP _ _ _ _ rgnP elgP _ iscP) = player st
      sequence_ [print (evt st),print (ecs st), print (mem st),print elgP,print iscP
                ,print ichSt,print (jps st)]
      (_,nrg) <- getRandomNumIO (5,rgnP)
      let i = keyCodeToChar kc 
          (x,y) = xyP 
          (wd,hi) = szSt
          ix = igx-wd
          (x',y') = keyCheck (wd,hi) (x,y) i
          p' = plMove (x',y') p
          (tx,ty) = xy p'
          (px,py) = (x+1,y+iy+1)
          (px',py') = (tx+1,ty+iy+1)
          p'' = if i==' ' then putOut p' else p'
          nst = checkEv 0 (elg p'') (evt st) st{player=p''{rgn=nrg}}
          (wd',_) = sz nst
          ix' = igx-wd'
      putGrid c (ix',iy) (gr (player nst))
      unless (ims nst) $ putMessageT c cvH (imx+msc nst,iy+hi+3) (msg nst)
      if ils nst || i=='n' then nextStage c ci nst{ims=False} 
                           else do
         let pxy = (px'+ix,py')
         if et (player nst)==' ' then putMozi c (chColors!!1) pxy [pl p'']
                                 else putMozi c (chColors!!2) pxy [pl p'']
         return nst
           where iniSt = ini st; impSt = imp st; imsSt = ims st; ichSt = ich st; szSt = sz st
                 imx = floor (cvW/wt) - 1; igx = floor (cvW/wg) - 2

--showLog :: Canvas -> String -> IO ()
--showLog c log = do
--   let els = divStr 25 log 
--       divStr i str
--         | length str<=i = [str]
--         | otherwise = take i str:divStr i (drop i str)
--   mapM_ (\(el,i) -> putMozi c (chColors!!1) (1,30+i) el) (zip els [0,1..])

nextStage :: Canvas -> CInfo -> State -> IO State 
nextStage c ci st = do
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
          inputLoop c ci 64 st{sz=nsz,player=np,msg="",jps = -1,ils=False,igc=False}

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

