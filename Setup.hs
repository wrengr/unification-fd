#!/usr/bin/env runhaskell
-- Cf. <http://www.mail-archive.com/haskell-cafe@haskell.org/msg59984.html>
-- <http://www.haskell.org/pipermail/haskell-cafe/2008-December/051785.html>

{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-missing-signatures #-}
module Main (main) where
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo (withPrograms)
import Distribution.Simple.Program        (userSpecifyArgs)
----------------------------------------------------------------

-- | Define __HADDOCK__ when building documentation.
main :: IO ()
main = defaultMainWithHooks
    $ simpleUserHooks `modify_haddockHook` \oldHH pkg lbi hooks flags -> do
        
        -- Call the old haddockHook with a modified LocalBuildInfo
        (\lbi' -> oldHH pkg lbi' hooks flags)
            $ lbi `modify_withPrograms` \oldWP ->
                userSpecifyArgs "haddock" ["--optghc=-D__HADDOCK__"] oldWP


modify_haddockHook  hooks f = hooks { haddockHook  = f (haddockHook  hooks) }
modify_withPrograms lbi   f = lbi   { withPrograms = f (withPrograms lbi)   }

----------------------------------------------------------------
----------------------------------------------------------- fin.
