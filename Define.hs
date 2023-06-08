module Define where

type Pos = (Int,Int)
type Fsize = Int          --Font Size
type Mana = Char 
type Cell = (Mana,Mode)
type Grid = [[Cell]]
type Stage = [(Pos,Cell)]
type Size = (Int,Int)
type Fpon = (Char,Func)
type Spon = (Int,Func2)
type Func = (Char->Char)
type Func2 = (Char->Char->Char)
type Def = (String,Integer) -- "String"=Integer 
type Msg = String
type Evt = (String,String)    --(Triger Event, Target Event)
type Mem = (String,String)    --memory (for event trigger)
type CInfo = ((Double,Double),(Double,Double)) 
    -- canvasWidth, canvasHeight, clientRectWidth, clientRectHeight

-- Fr: Free(can have) Bl: Block Ex: Exist(can't have) Mv: can push
-- Pn: Pon(function argument) Wn: Wander(random move) Cm: Come towards Player
-- DB: Dark Block DF: Dark Free
data Mode = Fr | Bl | Ex | Mv | Pn | Wn | Cm | DB | DF deriving (Eq,Show)

data Dir = Up | Dw | Lf | Rt | Cn deriving (Eq,Show)

data Play = Play {xy:: !Pos,
                  gr:: !Grid,         
                  pl:: !Char,           -- Player Appearance
                  et:: !Mana,           -- That Player Eats
                  sn:: !Int,            -- Stage Number
                  rgn:: !Int,           -- Random Number Generator
                  elg:: !String,        -- Event Log
                  iw:: !Bool,           -- Wandering People?
                  isc:: !Bool           -- Stage Clear?
                 } deriving (Eq,Show)

data State = State {player:: !Play,
                    sz:: !Size,     -- 
                    msg:: !Msg,     -- Messages
                    evt:: ![Evt],   -- Events
                    ecs:: ![Int],   -- Event Counts
                    mem:: ![Mem],   -- Memories
                    mps:: !Pos,     -- Message Position
                    mct:: !Int,     -- Message Count
                    mcl:: !Int,     -- Message Color Number
                    msc:: !Int,     -- Message Scroll Depth 
                    jps:: !Int,     -- Stage Number when Jump Stage
                    chd:: ![(String,String)],  -- Choice Data (Choice Sentence, Target Msg)
                    chn:: !Int,     -- Choice Number
                    ils:: !Bool,    -- Leave Stage?
                    igc:: !Bool,    -- Game Clear?
                    ims:: !Bool,     -- Message Show?
                    imp:: !Bool,     -- Message Pause?
                    itc:: !Bool,     -- Touch Is True?
                    ini:: !Bool,     -- No Input?
                    ich:: !Bool,     -- Choice Mode?
                    db:: !String,    --for debug
                    ch:: !Char       --optional
                   } deriving (Eq,Show)

iy :: Int
iy = 2

wg, hg, wt, ht :: Double 
wg = 16; hg = 20; wt = 28; ht = 20 -- grid width & height , tategaki letters width & height

nfs, rfs :: Int
nfs = 20; rfs = 8 -- normal font size, rubi font size

cvT :: Double
cvT = 10  --trim(yohaku)

