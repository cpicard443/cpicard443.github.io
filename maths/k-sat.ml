type litteral = |V of int (* variable *)
                |NV of int;; (* négation de variable *)

type clause = litteral list;;
type fnc = clause list;;
type trileen = |Vrai
               |Faux
               |Indet;;

type formule =
  |Var of int
  |Non of formule
  |Et of formule * formule
  |Ou of formule * formule;;

(*Quelques formules pour vérifier que tout marche bien*)
let f1 = [[V(1)];[NV(2)]];;
let g1 = [[NV(1)];[V(1)]];;
let f2 = [[V(0);V(1)];[V(1);V(2)]];;
let f = [[V(0)];[V(1);NV(0)]];;

(*Pour récupérer l'indice maximale des variables utilisées*)
let var_max f =
  let rec aux m c = match c with
    |[]->0
    |V(x)::t->max (max x m) (aux m t)
    |NV(x)::t->max (max x m) (aux m t)
  in
  List.fold_left aux 0 f
;;

(*Résolution de 1-SAT*)
let un_sat f =
  let n = var_max f in
  let t = Array.make (n+1) Indet in
  let satisfiable = ref true in
  let aux c = match c with
    |[]->()
    |V(x)::[]->if t.(x) = Faux then
                 satisfiable := false
               else
                 t.(x)<-Vrai
    |NV(x)::[]->if t.(x) = Vrai then
                 satisfiable := false
               else
                 t.(x)<-Faux
    |_->failwith "trop de litteral dans la clause"
  in
  List.iter aux f;
  !satisfiable
;;

let dfs g =
  let n = Array.length g in
  let marquage = Array.make n false in
  let l = ref [] in
  let rec aux e =
    if not marquage.(e) then
      begin
        marquage.(e)<-true;
        List.iter aux g.(e);
        l:=e::(!l);
      end
    else
      ()
  in
  for i=0 to n-1 do
    if not marquage.(i) then
      aux i
  done;
  !l
;;

let transpose g =
  let n = Array.length g  in
  let g2 = Array.make n [] in
  let rec aux p l = match l with
    |[]->()
    |h::t->
      begin
        g2.(h)<-p::g2.(h);
        aux p t
      end
  in
  for i=0 to n-1 do
    aux i g.(i)
  done;
  g2
;;


let kosaraju g =
  let l = dfs g in
  let g2 = transpose g in
  let n = Array.length g in
  let cfc = Array.make n (-1) in
  let cpt = ref 0 in
  let rec parcours e =
    let k = !cpt in
    if cfc.(e)=(-1) then
      begin
        cfc.(e)<-k;
        List.iter parcours g2.(e);
      end
    else
      ()
  in
  let rec aux l = match l with
    |[]->()
    |u::t->if cfc.(u) = (-1) then
             begin
               parcours u;
               cpt:=(!cpt)+1;
               aux t
             end
           else
             aux t         
  in
  aux l;
  cfc
;;

let deux_sat_vers_graphe f =
  let n = var_max f in
  let g = Array.make (2*n+2) [] in
  let aux c = match c with
    |[]->()
    |V(x)::[]->g.(2*x+1)<-(2*x)::g.(2*x+1)
    |NV(x)::[]->g.(2*x)<-(2*x+1)::g.(2*x)
    |V(x)::V(y)::[]->
      begin
        g.(2*x+1)<-(2*y)::g.(2*x+1);
        g.(2*y+1)<-(2*x)::g.(2*y+1);
      end
    |V(x)::NV(y)::[]->
      begin
        g.(2*x+1)<-(2*y+1)::g.(2*x+1);
        g.(2*y)<-(2*x)::g.(2*y);
      end
    |NV(x)::V(y)::[]->
      begin
        g.(2*x)<-(2*y)::g.(2*x);
        g.(2*y+1)<-(2*x+1)::g.(2*y+1);
      end
    |NV(x)::NV(y)::[]->
      begin
        g.(2*x)<-(2*y+1)::g.(2*x);
        g.(2*y)<-(2*x+1)::g.(2*y);
      end
    |_->failwith "trop de littéraux dans la clause"
  in
  List.iter aux f;
  g
;;

(*Résolution de 2-SAT*)
let deux_sat f =
  let g = deux_sat_vers_graphe f in
  let cfc = kosaraju g in
  let n = Array.length g in
  let satisfiable = ref true in
  for i=0 to (n/2)-1 do
    if cfc.(2*i) == cfc.(2*i+1) then
      satisfiable := false
  done;
  !satisfiable
;;


let et a b =
  if a=Vrai && b=Vrai then
    Vrai
  else if a=Faux || b=Faux then
    Faux
  else
    Indet
;;

let ou a b =
  if a=Vrai || b=Vrai then
    Vrai
  else if a=Faux && b=Faux then
    Faux
  else Indet
;;

let non a =
  if a=Vrai then Faux
  else if a=Faux then Vrai
  else Indet
;;

let eval f t =
  let rec eval_clause c = match c with
    |[]->Vrai
    |V(x)::[]->t.(x)
    |NV(x)::[]->non t.(x)
    |V(x)::q->ou t.(x) (eval_clause q)
    |NV(x)::q->ou (non t.(x)) (eval_clause q)
  in
  List.fold_left (fun b c -> et b (eval_clause c)) Vrai f
;;


(*Résolution de k-SAT*)
let k_sat f =
  let n = var_max f in
  let t = Array.make (n+1) Indet in
  let rec aux k =
    if k=n+1 then true
    else
      begin
        t.(k)<-Vrai;
        if (eval f t)<>Faux && (aux (k+1)) then true
        else
          begin
            t.(k)<-Faux;
            if (eval f t)<>Faux && (aux (k+1)) then true
            else
              begin
                t.(k)<-Indet;
                false;
              end
          end
      end
  in
  aux 0,t
;;

        
                             
                  
                         
                 
        
