
-- Local Variables:
-- idris-packages: ("effects")
-- End:

module Main

import Effect.Random
import Effect.StdIO
import Exception

guess : Int -> { [STDIO] } Eff ()
guess target
    = do putStr "Guess: "
         case run {m=Maybe} (parseNumber 100 (trim !getStr)) of
              Nothing => do putStrLn "Invalid input"
                            guess target
              Just (v ** _) =>
                         case compare v target of
                             LT => do putStrLn "Too low"
                                      guess target
                             EQ => do putStrLn "You win!"
                             GT => do putStrLn "Too high"
                                      guess target

game : { [RND, STDIO] } Eff ()
game = do srand 123456789
          guess (fromInteger !(rndInt 0 100))

main : IO ()
main = run game
