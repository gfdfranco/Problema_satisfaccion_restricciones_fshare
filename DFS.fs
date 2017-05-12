module DFS
open System.Collections.Generic

// Estructuras de datos funcionales (no hay efectos secundarios)
let estrategia_dfs0<'s,'a> =
    {siguiente = Stack.pop
     agregar = Stack.push
     inicializar = Stack.push Stack.empty} : Busqueda.estrategia<'s,'a, Stack.stack<Busqueda.nodo<'s,'a>>>


// Estructuras de datos funcionales (no hay efectos secundarios)
// Recuerda estados visitados
let estrategia_dfs1<'s,'a when 's : comparison> =
    {siguiente = fun (estados, visitados) ->
                    let (x,estados) = Stack.pop estados
                    (x, (estados, visitados))
     agregar = fun (estados, visitados) n  -> 
                    if Set.contains n.estado visitados
                    then (estados, visitados)
                    else (Stack.push estados n, Set.add n.estado visitados)
     inicializar = fun n -> (Stack.push Stack.empty n, set [n.estado])} : Busqueda.estrategia<'s,'a, Stack.stack<Busqueda.nodo<'s,'a>> * Set<'s>>


// Estructuras de datos imperativas (efectos secundarios)
let estrategia_dfs2<'s,'a> =
    let estados = new Stack<Busqueda.nodo<'s,'a>>()
    let visitados = new HashSet<'s>()
//    let visitados = new SortedSet<'s>()
    {siguiente = fun ()  -> try
                             (Some (estados.Pop ()), ())
                            with | :? System.InvalidOperationException -> (None, ())
     agregar = fun () n  -> if visitados.Contains n.estado
                            then ()
                            else estados.Push n
                                 ignore (visitados.Add n.estado)
     inicializar = fun n -> estados.Push n
                            ignore (visitados.Add n.estado)} : Busqueda.estrategia<'s,'a, unit>

    

