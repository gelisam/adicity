Adicity
===

This is a Haskell DSL in which operation have known input and output adicities. That is, an i,j-adic operation has i inputs and j outputs, and values are represented as 0,1-adic operations.

As Conor McBride [explains](https://www.reddit.com/r/haskell/comments/3esx0e/what_is_the_difference_between_and/cticfot), in such a language it is possible to define a single operation which acts as both function composition and function application! Conor calls this operation "juxtaposition", but since I cannot overload Haskell's function application syntax, I call this operation `(<.<)`.

Here are two simple examples.

    -- | Depending on which (<.<) you interpret as function composition and which one you
    -- interpret as function application, you can interpret the adicity composition below
    -- as either of the following. They all give the same result.
    -- 
    -- >>> (+) (2 * 3) 4
    -- 10
    -- >>> ((+) . (* 2)) 3 4
    -- 10
    -- >>> n
    -- 10
    n :: Int
    n = runAdicity_0_1 $ adicity_2_1 (+) <.< adicity_2_1 (*)
                     <.< adicity_0_1 2 <.< adicity_0_1 3 <.< adicity_0_1 4

    -- |
    -- >>> (+1) . (*2) $ 3
    -- 7
    -- >>> (+1) $ (*2) 3
    -- 7
    -- >>> m
    -- 7
    m :: Int
    m = runAdicity_0_1 $ adicity_1_1 (+1) <.< adicity_1_1 (*2)
                     <.< adicity_0_1 3
