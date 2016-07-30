
-- Local Variables:
-- idris-packages: ("effects")
-- End:

module Main

import Effect.State
import Effect.StdIO

hello : { [STATE Int, STDIO] } Eff ()
hello = do putStr "Name? "
           putStrLn ("Hello " ++ trim !getStr ++ "!")
           update (+1)
           putStrLn ("I've said hello to: " ++ show !get ++ " people")
           hello

main : IO ()
main = run hello
