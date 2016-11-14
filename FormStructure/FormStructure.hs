{-# LANGUAGE OverloadedStrings #-}

module FormStructure.FormStructure (formItems) where

import           FormEngine.FormItem
import           FormStructure.Chapter0
import           FormStructure.Chapter1
import           FormStructure.Submit

formItems :: [FormItem]
formItems = prepareForm
             [ 
              ch0GeneralInformation
            , ch1DataProduction
            , submitForm
             ]