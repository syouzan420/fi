{-# LANGUAGE OverloadedStrings #-}
module Browser (chColors,cvRatio,clFields,flToKc,fields,
                tcStart,tcEnd,touchIsTrue) where

import Haste.Events (onEvent,preventDefault,KeyEvent(..),KeyData(..))
import Haste.Graphics.Canvas(Canvas,Color(RGB),Rect(..))
import Haste.DOM (document)
import Haste.Foreign (ffi)
import Define (State(itc),cvW,cvH)

chColors :: [Color]
chColors = [RGB 0 0 0,RGB 255 204 153,RGB 255 153 204,RGB 153 255 255] 

canvasW :: Canvas -> IO Double 
canvasW = ffi "(function(cv){return cv.width})"

canvasH :: Canvas -> IO Double 
canvasH = ffi "(function(cv){return cv.height})"

crecW :: Canvas -> IO Double 
crecW = ffi "(function(cv){return cv.getBoundingClientRect().width})"

crecH :: Canvas -> IO Double 
crecH = ffi "(function(cv){return cv.getBoundingClientRect().height})"

cvRatio :: Canvas -> IO (Double,Double)
cvRatio c = do
  cWidth <- canvasW c
  cHeight <- canvasH c
  rcW <- crecW c
  rcH <- crecH c
  return (cWidth/rcW,cHeight/rcH)

clFields :: Double -> Double -> [Rect] -> Int
clFields _ _ [] = 0 
clFields p q (Rect x y w h:rs) =
  if p>x && p<x+w && q>y && q<y+h then 1 else 1+clFields p q rs

flToKc :: Int -> Int
flToKc field = case field of
                 1 -> 72; 2 -> 74; 3 -> 75; 4 -> 76; 5 -> 32; _ -> 64;

fields :: [Rect]
fields = let h = cvH
             w = cvW
          in [Rect 0 100 100 (h-100),
              Rect 0 (h-100) w 100,
              Rect 0 0 w 100,
              Rect (w-100) 100 100 (h-100),
              Rect 100 100 (w-200) (h-200)]

tcStart :: State -> IO State
tcStart st = if itc st then preventDefault >> return st
                         else return st

tcEnd :: State -> IO State
tcEnd st = return st{itc=False}

touchIsTrue :: State -> IO State
touchIsTrue st = return st{itc=True}
