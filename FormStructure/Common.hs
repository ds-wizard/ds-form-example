{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Common where
#ifndef __HASTE__
import           Data.Text (pack)
#endif 
import           FormEngine.FormItem

remark :: FormItem
remark = SimpleGroup
  { sgDescriptor = FIDescriptor
    { iLabel = Just "Other"
    , iNumbering = NoNumbering
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = True
    }
  , sgLevel = 0
  , sgItems = [ TextFI
                { tfiDescriptor = FIDescriptor
                  { iLabel = Just "Your comments"
                  , iNumbering = NoNumbering
                  , iIdent = Nothing
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Just "Text field long description"
                  , iLink = Nothing
                  , iRules = []
                  , iMandatory = False
                  }
                }
              ]
  }

