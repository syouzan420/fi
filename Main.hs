import Haste (setTimer,Interval(Once,Repeat))
import Haste.Events (onEvent,preventDefault,KeyEvent(..),KeyData(..),
                     MouseEvent(..),MouseData(..),TouchEvent(..),TouchData(..))
import Haste.DOM (document,elemById,fromElem)
import Data.IORef(newIORef,readIORef,writeIORef)
import CvLoop (initiate,inputLoop,mouseClick)
import OutToCanvas (putMessageG)
import Browser (cvRatio,tcStart,tcEnd,touchIsTrue)

main :: IO ()
main = do
  Just ce <- elemById "canvas2"
  Just c <- fromElem ce
  st <- initiate c
  state <- newIORef st
  onEvent document KeyDown $ \(KeyData kc _ _ _ _) -> do
    preventDefault
    readIORef state >>= inputLoop c kc >>= writeIORef state
  onEvent ce Click $ \(MouseData (x,y) _ _) -> do
    (rtx,rty) <- cvRatio c
    let nx = fromIntegral x*rtx
        ny = fromIntegral y*rty
    readIORef state >>= mouseClick c nx ny >>= writeIORef state
  onEvent ce TouchStart $ \(TouchData {}) -> do
    readIORef state >>= tcStart >>= writeIORef state
  onEvent ce TouchEnd $ \(TouchData {}) -> do
    readIORef state >>= touchIsTrue >>= writeIORef state
    setTimer (Once 100) $ readIORef state >>= tcEnd >>= writeIORef state
    return ()
  setTimer (Repeat 50) $
    readIORef state >>= putMessageG c >>= writeIORef state
  return ()

