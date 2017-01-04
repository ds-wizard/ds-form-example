import FormEngine.Perch as P
import Haste
import Haste.Events
import Haste.DOM
import Prelude hiding (div)

main :: IO ()
main = do
--  _ <- withElem "idelem" $ \e -> setAttr e "style" "background:red"
  _ <- withElem "idelem" $ build $ do
    P.setHtml (div "abcd") "kokot"
  --  div $ div $ p ! atr "style" "color:red" $ "world"
--    P.attr (div "abcd") ("style", "color:red")

--  _ <- withElem "idelem" $ build $ do
--    div $ do
--      _ <- addEvent this Click $ \_ -> alert "hello, world!"
--      div $ do
--        p "hello"
--        p ! atr "style" "color:red" $ "world"
  return ()
