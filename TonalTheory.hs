
module TonalTheory where

import Euterpea
import Data.List hiding (transpose)

type Key = (PitchClass, Mode)

data Direction = Ascending | Descending
    deriving (Show,Eq,Enum)

pcEq :: PitchClass -> PitchClass -> Bool
pcEq x y = (pcToInt x `mod` 12) == (pcToInt y `mod` 12)

pitchEq :: Pitch -> Pitch -> Bool
pitchEq x y = (absPitch x) == (absPitch y)

transPC :: Int -> PitchClass -> PitchClass
transPC i p = fst $ trans i (p,4)

notePitch :: Music Pitch -> Pitch
notePitch (Prim (Note _ p)) = p
notePitch _                 =
    error "notePitch: Non-note argument"

modeIntervals :: Mode -> [Int]
modeIntervals Major      = [2,2,1,2,2,2,1]
modeIntervals Minor      = [2,1,2,2,1,2,2]
modeIntervals Ionian     = [2,2,1,2,2,2,1]
modeIntervals Dorian     = [2,1,2,2,2,1,2]
modeIntervals Phrygian   = [1,2,2,2,1,2,2]
modeIntervals Lydian     = [2,2,2,1,2,2,1]
modeIntervals Mixolydian = [2,2,1,2,2,1,2]
modeIntervals Aeolian    = [2,1,2,2,1,2,2]
modeIntervals Locrian    = [1,2,2,1,2,2,2]

scaleDegree :: Key -> Int -> PitchClass
scaleDegree (t,m) i = 
    let ints  = modeIntervals m
        steps = sum $ take (i -1) ints
    in transPC steps t

offsetScale :: Key -> [Int] -> PitchClass -> [Int]
offsetScale (t,m) is pc =
    let is'   = cycle is
        tonic = pcToInt t
        base  = pcToInt pc + 12     -- ensure monotonic increase of ints, make enharmonic eqs work
        offM  = findIndex (>= base) $ scanl (+) tonic is'
        off   = maybe (error "offsetScale") id offM   -- error case not possible
    in drop off is'

transDiatonic :: Key -> Int -> Pitch -> Pitch
transDiatonic (t,m) i (p,o) =
    let is     = modeIntervals m
        len    = length is
        (os,s) = i `divMod` len     -- if i is negative, os < 0 and s >= 0
        is'    = offsetScale (t,m) is p
        steps  = (12 * os) + (sum $ take s is')
    in trans steps (p,o)

-- Chromatic version
stepMotion :: Dur -> Music Pitch -> Music Pitch -> Music Pitch
stepMotion d n1@(Prim (Note _ p1)) n2@(Prim (Note _ p2)) =
    let ap1   = absPitch p1
        ap2   = absPitch p2
        ints  = if ap1 <= ap2 
                then [ap1+1 .. ap2-1]
                else [ap1-1, ap1-2 .. ap2+1]
        steps = line $ map (note d . pitch) ints
    in n1 :+: steps :+: n2
stepMotion _ _ _ = error "stepMotion: non-note argument"

-- Diatonic version
stepMotiond :: Key -> Dur -> Music Pitch -> Music Pitch -> Music Pitch
stepMotiond k d n1@(Prim (Note _ p1)) n2@(Prim (Note _ p2)) = 
    let ap1   = absPitch p1
        ap2   = absPitch p2
        td    = flip (transDiatonic k) p1
        ps    = if ap2 >= ap1
                then takeWhile ((< ap2) . absPitch) $ map td [1..]
                else takeWhile ((> ap2) . absPitch) $ map td [-1,-2..]
        steps = line $ map (note d) ps
    in n1 :+: steps :+: n2
stepMotiond _ _ _ _ = error "stepMotiond: non-note argument"

triadPitches :: Key -> Int -> Octave -> [Pitch]
triadPitches key degree o =
    let transd = flip (transDiatonic key) root
        rpc    = scaleDegree key degree
        root   = (rpc,o)
        third  = transd 2 
        fifth  = transd 4
    in [root, third, fifth]

scaleTriad :: Key -> Int -> Octave -> Dur -> Music Pitch
scaleTriad key degree o d = chord $ map (note d) ps
    where ps = triadPitches key degree o

-- exact equivalent of Euterpea's lineToList
chordToList :: Music a -> [Music a]
chordToList (Prim (Rest 0))    = []
chordToList (n :=: ns)         = n : chordToList ns
chordToList _                  =
    error "chordToList: argument not created by function chord"

-- handle lines/chords without terminating zero-dur rests 
-- (as well as those with them)
lineToList1 :: Music a -> [Music a]
lineToList1 (Prim (Rest 0)) = []
lineToList1 p@(Prim _)      = [p]
lineToList1 (n :+: ns)      = n : lineToList1 ns
lineToList1 _          =
    error "lineToList1: non-line argumnet"
 
chordToList1 :: Music a -> [Music a]
chordToList1 (Prim (Rest 0)) = []
chordToList1 p@(Prim _)      = [p]
chordToList1 (n :=: ns)      = n : chordToList1 ns
chordToList1 _          =
    error "chordToList1: non-chord argumnet"

brokenChord :: Music a -> Music a
brokenChord = line . chordToList1

changeDur :: Dur -> Music a -> Music a
changeDur d (Prim (Note _ p)) = Prim (Note d p)
changeDur d (Prim (Rest _))   = Prim (Rest d)
changeDur _ _ = error "changeDur: non-primitive argument"

-- Notes in list cannot be transposed
sortNotes :: Direction -> [Music Pitch] -> [Music Pitch]
sortNotes d ns = sortOn k ns
    where toPitch m = case m of
              (Prim (Note _ p)) -> absPitch p
              (Prim (Rest _))   -> 0
          k         = case d of 
              Ascending  -> toPitch
              Descending -> negate . toPitch

arpeggiate :: Direction -> Music Pitch -> Music Pitch
arpeggiate d m@(m1 :=: m2) = line $ sortNotes d $ chordToList1 m
arpeggiate d (Modify c m)  = Modify c (arpeggiate d m)
arpeggiate _ _             =
    error "arpeggiate: non-chord argument"

arpeggiato :: Direction -> Music Pitch -> Music Pitch
arpeggiato d m@(m1 :=: m2)  = 
    let arp        = sortNotes d $ chordToList1 m
        arpd       = dur m
        delta      = arpd / (fromIntegral $ length arp) -- pattern match for m ensures denom isn't 0
        offsets    = [0, delta .. arpd]
        scaled o n = offset o $ changeDur (arpd - o) n 
    in chord $ zipWith scaled offsets arp
arpeggiato d (Modify c m)   = Modify c (arpeggiato d m)
arpeggiato _ _              =
    error "arpeggiato: non-chord argument"

-- Parameterize fraction of first note duration ?
mordent :: Int -> Music Pitch -> Music Pitch
mordent i (Prim (Note d p)) = 
    let md1  = d * (1/8)
        md2  = d * (3/4)
        mord = trans i p
    in line [note md1 p, note md1 mord, note md2 p]
mordent i (Modify c m)      = Modify c (mordent i m)
mordent _ _                 = 
    error "mordent: non-note argument"

mordentd :: Key -> Int -> Music Pitch -> Music Pitch
mordentd key i (Prim (Note d p)) = 
    let md1  = d * (1/8)
        md2  = d * (3/4)
        mord = transDiatonic key i p
    in line [note md1 p, note md1 mord, note md2 p]
mordentd key i (Modify c m)      = Modify c (mordentd key i m)
mordentd _ _ _                   = 
    error "mordentd: non-note argument"

-- Version of mMap for functions that need a Music value as input
mMap1 :: (Music a -> Music b) -> Music a -> Music b
mMap1 f = mFold (pMap1 f) (:+:) (:=:) Modify

pMap1 :: (Music a -> Music b) -> Primitive a -> Music b
pMap1 f (Note d x)  = f (Prim (Note d x))
pMap1 f (Rest d)    = Prim (Rest d)

-- Version of mMap for functions that need a Music value as input,
-- rests inclusive
mMap2 :: (Music a -> Music b) -> Music a -> Music b
mMap2 f = mFold (f . Prim) (:+:) (:=:) Modify

