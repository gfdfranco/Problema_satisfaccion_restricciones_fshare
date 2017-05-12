module Robot

open CSP

type variable = A | B | C | D | E | F

type dominio = Primero | Segundo | Tercero | Cuarto | Quinta

type restriccion = DiferenteDe of variable * variable 
                    | DiferenteDominioDe of variable * variable * dominio
                    | IgualDominioDe of variable * variable * dominio
                    | IgualDe of variable * variable

let vars = [ A; B; C; D; E; F ]
let d = [ Primero; Segundo; Tercero; Cuarto; Quinta ]
let restricciones = 
    [ 
      IgualDominioDe(E, E, Primero)
      IgualDe(A, F)
      DiferenteDominioDe(B, B, Segundo)
      DiferenteDominioDe(B, B, Cuarto)
      DiferenteDominioDe(C, C, Segundo)
      DiferenteDominioDe(D, D, Segundo)
      DiferenteDe(B, C)
      DiferenteDe(B, D)
      DiferenteDe(B, E)
      DiferenteDe(B, F)
      DiferenteDe(C, D)
      DiferenteDe(C, F)
      DiferenteDe(D, A)
      DiferenteDe(D, E)
      DiferenteDe(E, A)
      DiferenteDe(E, C)
    ]

let evalua restriccion estado =
    match restriccion with
        |DiferenteDe (v, v') -> 
            match (Map.tryFind v estado, Map.tryFind v' estado) with
                | (Some w, Some w') -> if List.length w = 1 && List.length w' = 1
                                       then w <> w'
                                       else true
                | _ -> true
        |DiferenteDominioDe (v,v',variable) -> 
            match (Map.tryFind v estado, Map.tryFind v' estado) with
                | (Some w, Some w') -> if List.length w = 1 
                                       then w.Head <> variable
                                       else true
                | _ -> true
        |IgualDominioDe (v,v',variable) -> 
            match (Map.tryFind v estado, Map.tryFind v' estado) with
                | (Some w, Some w') -> if List.length w = 1 
                                       then w.Head = variable
                                       else true
                | _ -> true
        |IgualDe (v, v') -> 
            match (Map.tryFind v estado, Map.tryFind v' estado) with
                | (Some w, Some w') -> if List.length w = 1 && List.length w' = 1
                                       then w = w'
                                       else true
                | _ -> true

let hacer_restriccion restriccion : CSP.restriccion<variable, dominio> =
    match restriccion with
        |DiferenteDe (v, v') -> Binaria ((v, v'), evalua restriccion)
        |DiferenteDominioDe (v,v',variable) -> Binaria ((v, v'), evalua restriccion)
        |IgualDominioDe (v,v',variable) -> Binaria ((v, v'), evalua restriccion)
        |IgualDe (v, v') -> Binaria ((v, v'), evalua restriccion)


let csp = {vars = [ A; B; C; D; E; F ]
           doms = [d; d; d; d; d; d]
           restricciones = List.map hacer_restriccion restricciones} : csp<variable, dominio>

let test () = 
    CSP.backtracking csp
