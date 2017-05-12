module Stack

type 'a stack = 'a list

let empty = []

let push stack x = x :: stack

let pop = function
    | x :: stack -> (Some x, stack)
    | [] -> (None, [])
