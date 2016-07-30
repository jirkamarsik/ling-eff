
-- Local Variables:
-- idris-packages: ("effects")
-- End:

module Exception

import Effect.Exception

data Err = NotANumber | OutOfRange

Bounded : Int -> Type
Bounded x = (n : Int ** So (n >= 0 && n <= x))

parseNumber : (x : Int) -> String -> { [EXCEPTION Err] } Eff (Bounded x)
parseNumber x str
   = if all isDigit (unpack str)
        then let num = cast str in
             case choose (num >=0 && num <= x) of
                Left p => pure (num ** p)
                Right p => raise OutOfRange
        else raise NotANumber
