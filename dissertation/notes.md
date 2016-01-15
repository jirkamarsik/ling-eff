* Maybe use exclamation marks in the names of operations?


F ::= []
    | (f M)
    | (V f)
    | (Shift f)

c ::= f
    | (Reset c)

V ::= (\x. M)
    | X
M,n ::= V
      | (M N)
      | (shift M)
      | (reset m)

C[(\x. M) N]  ->  C[M[x:=n]]

c[(Reset v)] -> c[v]

c[(reset f[shift v])]
->
c[(v (\x. (reset (f[x])))]


[| (reset m) |] =
(| shift: (\c k. c k) |) M

[| (Shift m) |] =
M >>= (\m'. shift! m')


M -> N    =>    [|M|] ->> [|N|]

[| F[Shift v] |]
=
Shift v (\x. [| f[x] |])


f = (V f')
[| f[x] |] = (v' [| f'[x] |])

[| F[Shift U] |]
= [| (V f'[shift u]) |]
= [| v |] >>= (\a. [| f'[shift u] |] >>= (\B. a b))
= [| f'[shift u] |] >>= (\b. v' b)
= (shift u (\x. [| f'[x] |])) >>= (\b. V' b)
= shift u (\x. (\b. V' B) ([| f'[x] |]))
= shift u (\x. (v' [| f'[x] |]))
= shift u (\x. [| f[x] |] )

[| v |] = eta v'
[| f'[shift u] |] = shift u (\x. [| f'[x] |])


