{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      :  Seal.Lang.Clj.Native.Time
-- Copyright   :  (C) 2016 Stuart Popejoy
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Stuart Popejoy <stuart@kadena.io>
--
-- Date/time built-ins.
--

module Seal.Lang.Clj.Native.Time
    ( timeDefs
    , defAddTime
    , defFormatTime
    , parseTimeDef
    , timeDef
    ) where

import Seal.Prelude
import Data.Thyme
import Data.Decimal
import System.Locale
import Data.AffineSpace

import Seal.Lang.Clj.Types.Runtime
import Seal.Lang.Clj.Native.Internal


timedoc :: Text
timedoc = "See [\"Time Formats\" docs](seal-reference.html#time-formats) for supported formats."

defAddTime :: HasEval env => NativeDef env
defAddTime = defRNative "add-time" addTime
  ( funType tTyTime [("time", tTyTime),("seconds", tTyDecimal)]
  <> funType tTyTime [("time", tTyTime),("seconds", tTyInteger)]
  )
  $ "Add SECONDS to TIME; SECONDS can be integer or decimal. "
  <> "`(add-time (time \"2016-07-22T12:00:00Z\") 15)`"
  where

    -- addTime :: RNativeFun env
    addTime _ [TLiteral (LTime t) _,TLiteral (LDecimal r) _]
      = return $ doTimeAdd t r
    addTime _ [TLiteral (LTime t) _,TLitInteger n]
      = return $ doTimeAdd t (fromIntegral n)
    addTime i as = argsError i as

    doTimeAdd :: UTCTime -> Decimal -> Term Name
    doTimeAdd t r = toTerm (t .+^ fromSeconds r)

defFormatTime :: HasEval env => NativeDef env
defFormatTime = defRNative "format-time" formatTime'
  (funType tTyString [("format", tTyString),("time", tTyTime)])
  $ "Format TIME using FORMAT. " <> timedoc
  <> "`(format-time \"%F\" (time \"2016-07-22T12:00:00Z\"))`"
  where

    formatTime' _ [TLitString fmt,TLiteral (LTime t) _] =
      return $ toTerm $ toText $ formatTime defaultTimeLocale (toString fmt) t
    formatTime' i as = argsError i as

parseTimeDef :: HasEval env => NativeDef env
parseTimeDef = defRNative "parse-time" parseTime'
  (funType tTyTime [("format", tTyString),("utcval", tTyString)])
  $ "Construct time from UTCVAL using FORMAT. " <> timedoc
  <> "`(parse-time \"%F\" \"2016-09-12\")`"
  where

    parseTime' i [TLitString fmt,TLitString s] =
      case parseTime defaultTimeLocale (toString fmt) (toString s) of
        Nothing -> evalError' i $ "Failed to parse time '" ++ toString s ++ "' with format: " ++ toString fmt
        Just t -> return (tLit (LTime t))
    parseTime' i as = argsError i as

timeDef :: HasEval env => NativeDef env
timeDef = defRNative "time" time
  (funType tTyTime [("utcval", tTyString)])
  $ "Construct time from UTCVAL using ISO8601 format ("
  <> toText simpleISO8601 <> "). "
  <> "`(time \"2016-07-22T11:26:35Z\")`"
  where

    time i [TLitString s] =
      case parseTime defaultTimeLocale simpleISO8601 (toString s) of
        Nothing -> evalError' i $
          "Invalid time, expecting '" ++ simpleISO8601 ++ "': " ++ toString s
        Just t -> return (tLit (LTime t))
    time i as = argsError i as

timeDefs :: HasEval env => NativeModule env
timeDefs = ("Time", defs)
  where
    defs =
        [ timeDef 
        , parseTimeDef 
        , defAddTime 
        , defRNative "diff-time" diffTime
            (funType tTyDecimal [("time1", tTyTime),("time2", tTyTime)])
            $ "Compute difference between TIME1 and TIME2 in seconds. "
            <> "`(diff-time (parse-time \"%T\" \"16:00:00\") "
            <> "(parse-time \"%T\" \"09:30:00\"))`"
        , defRNative "minutes" (timeMult 60)
            multType
            $ "N minutes, for use with 'add-time'. "
            <> "`(add-time (time \"2016-07-22T12:00:00Z\") (minutes 1))`"
        , defRNative "hours" (timeMult $ 60 * 60)
            multType
            $ "N hours, for use with 'add-time' "
            <> "`(add-time (time \"2016-07-22T12:00:00Z\") (hours 1))`"
        , defRNative "days" (timeMult $ 60 * 60 * 24)
            multType
            $ "N days, for use with 'add-time' "
            <> "`(add-time (time \"2016-07-22T12:00:00Z\") (days 1))`"
        , defFormatTime 
        ]
    multType = funType tTyDecimal [("n", tTyDecimal)]
        <> funType tTyDecimal [("n", tTyInteger)]



diffTime :: HasEval env => RNativeFun env
diffTime _ [TLiteral (LTime t1) _,TLiteral (LTime t2) _] = return $ toTerm (toSeconds (t1 .-. t2) :: Decimal)
diffTime i as = argsError i as

timeMult :: HasEval env => Decimal -> RNativeFun env
timeMult m _ [TLitInteger n] = return $ toTerm (fromIntegral n * m)
timeMult m _ [TLiteral (LDecimal d) _] = return $ toTerm (d * m)
timeMult _ i as = argsError i as
