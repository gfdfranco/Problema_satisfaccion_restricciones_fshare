module CSP


type estado<'variable,'valor when 'variable: comparison and
                                  'valor   : comparison>
    = Map<'variable, 'valor list>


type restriccion<'variable,'valor when 'variable: comparison and
                                       'valor   : comparison>
    =  Binaria of ('variable * 'variable) * (estado<'variable,'valor> -> bool)
     | NAria of ('variable list) * (estado<'variable,'valor> -> bool)

let eval r =
    match r with
        | Binaria (_, f) -> f
        | NAria (_, f) -> f

type csp<'variable,'valor when 'variable: comparison and
                               'valor   : comparison> =
    {vars : 'variable list
     doms : 'valor list list
     restricciones : restriccion<'variable,'valor> list
    }

let inicio (csp : csp<'variable,'valor>) =
    csp.doms |> List.map2 (fun v dom -> (v, dom)) csp.vars
             |> List.fold (fun m (v,dom) -> Map.add v dom m) Map.empty

let meta (csp : csp<'variable,'valor>) (estado : estado<'variable, 'valor>) =
    let i = estado |> Map.fold (fun p v dom -> (v,dom) :: p) []
                   |> List.filter (fun (_, dom) -> List.length dom = 1)
                   |> List.length
    i = List.length csp.vars

let degree var csp =
    List.fold (fun c r -> match r with
                            | Binaria ((v,v'), _) ->
                                if var = v || var = v'
                                then c + 1
                                else c
                            | NAria (vs, _) -> 
                                if List.exists (fun v -> v = var) vs
                                then c + 1
                                else c) 0 csp.restricciones

let ac3 csp estado =
    let incidencias v =
        List.fold (fun rs r -> match r with
                                | Binaria ((p, q), _) ->
                                    if v = p
                                    then (r, (q, v)) :: rs
                                    elif v = q
                                    then (r, (q, v)) :: rs
                                    else rs
                                | NAria _ -> rs) [] csp.restricciones
    let remover estado (restriccion, (v,v')) =
        estado |> Map.find v
               |> List.fold (fun (modificado, dom) x ->
                        let estado' = Map.add v [x] estado
                        if List.exists (fun y -> let estado'' = Map.add v' [y] estado'
                                                 eval restriccion estado'') (Map.find v' estado)
                        then (modificado, x::dom)
                        else (true, dom)) (false, [])
    let rec ac3_aux estado restricciones =
        match restricciones with
            | (r, (v,v')) :: restricciones ->
                let (modificado, dom) = remover estado (r, (v,v'))
                if modificado
                then let estado = Map.add v dom estado
                     let arcos = incidencias v
                     ac3_aux estado (arcos @ restricciones)
                else ac3_aux estado restricciones
            | [] -> estado
    csp.restricciones
        |> List.collect (fun r -> match r with
                                    | Binaria ((p,q), _) ->
                                        [(r, (p,q)); (r, (q,p))]
                                    | NAria _ -> [])
        |> ac3_aux estado

let sucesores (csp : csp<'variable,'valor>) (estado : estado<'variable, 'valor>) =
    estado |> Map.fold (fun p v dom -> (v,dom) :: p) []
           |> (fun x -> printfn "%A" estado
                        x)
           |> List.filter (fun (_, dom) -> List.length dom <> 1)
           |> (fun l -> match l with
                            | _ :: _ -> 
                                l |> List.minBy (fun (var, dom) -> (List.length dom, -degree var csp))
                                  |> (fun (var, dom) -> 
                                        List.choose (fun v -> let s = estado |> Map.add var [v]
                                                                             |> ac3 csp
                                                              if List.forall (fun r -> eval r s) csp.restricciones &&
                                                                 not (Map.exists (fun _ vs -> List.isEmpty vs) s)
                                                              then Some ((), s)
                                                              else None) dom)
                            | _ -> [])

let backtracking (csp : csp<'variable,'valor>) =
    let problema = 
        {inicio = inicio csp
         meta = meta csp
         sucesores = sucesores csp
         costo = fun _ _ _ -> 1
        } : Busqueda.problema<estado<'variable,'valor>, unit>
    match Busqueda.busqueda DFS.estrategia_dfs1<estado<'variable,'valor>,unit> problema with
        | Some n -> Some n.estado
        | None   -> None
