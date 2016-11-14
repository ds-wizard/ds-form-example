{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Prelude
import           Data.Maybe (isNothing, catMaybes)

import           FormEngine.JQuery (ready, errorIO)
import           FormStructure.FormStructure as Structure
import           FormEngine.FormElement.FormElement as Element
import           Form

main :: IO ()
main = ready $ do
  let tabMaybes = map (Element.makeChapter Nothing) Structure.formItems
  if any isNothing tabMaybes then do
    errorIO "Error generating tabs"
    return ()
  else do
    let tabs = catMaybes tabMaybes
    generateForm tabs


