module Email (User, Host, Email(), at, render) where
type User  = String
type Host  = String
data Email = E User Host

instance Show Email where
  show = render

eUser :: Email -> User
eUser (E u h) = u

eHost :: Email -> Host
eHost (E u h) = h

render :: Email -> String
render (E u h) = u ++ "@" ++ h

at :: User -> Host -> Maybe Email
at "" h  = Nothing
at u  "" = Nothing
at u  h  = Just (E u h)
