(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)


module E = Errormsg
open Trace
open Pretty

(* Output management *)
let out : out_channel option ref = ref None
let close_me = ref false

let close_output _ =
  match !out with
    None -> ()
  | Some o -> begin
      flush o;
      if !close_me then close_out o else ();
      close_me := false
  end

let set_output filename =
  close_output ();
  let out_chan = try open_out filename 
    with Sys_error msg -> 
    (output_string stderr ("Error while opening output: " ^ msg); exit 1) in
  out := Some out_chan;
  Whitetrack.setOutput out_chan;
  close_me := true

   (* Signal that we are in MS VC mode *)
let setMSVCMode () =
  Cprint.msvcMode := true

(* filename for patching *)
let patchFileName : string ref = ref ""      (* by default do no patching *)

(* patching file contents *)
let patchFile : Cabs.file option ref = ref None

(* whether to print the patched CABS files *)
let printPatchedFiles : bool ref = ref false

(* whether to print a file of prototypes after parsing *)
let doPrintProtos : bool ref = ref false

(* this seems like something that should be built-in.. *)
let isNone (o : 'a option) : bool =
begin
  match o with
  | Some _ -> false
  | None -> true
end

let printNotice = ref false

(*
** Argument definition
*)
let args : (string * Arg.spec * string) list =
[
  "--cabsonly", Arg.String set_output, "<fname> CABS output file name";
  "--printComments", Arg.Unit (fun _ -> Cprint.printComments := true),
             " print cabs tree structure in comments in cabs output";
  "--patchFile", Arg.String (fun pf -> patchFileName := pf),
             "<fname> name the file containing patching transformations";
  "--printPatched", Arg.Unit (fun _ -> printPatchedFiles := true),
             " print patched CABS files after patching, to *.patched";
  "--printProtos", Arg.Unit (fun _ -> doPrintProtos := true),
             " print prototypes to safec.proto.h after parsing";
  "--printNotice", Arg.Set printNotice,
             " include a comment saying printed by FrontC";
]

exception ParseError of string
exception CabsOnly

(* parse, and apply patching *)
let rec parse_to_cabs fname =
begin
  (* parse the patch file if it isn't parsed already *)
  if ((!patchFileName <> "") && (isNone !patchFile)) then (
    (* parse the patch file *)
    patchFile := Some(parse_to_cabs_inner !patchFileName);
    if !E.hadErrors then
      (failwith "There were parsing errors in the patch file")
  );

  (* now parse the file we came here to parse *)
  let cabs = parse_to_cabs_inner fname in
  if !E.hadErrors then 
    E.s (E.error "There were parsing errors in %s" fname);

  (* and apply the patch file, return transformed file *)
  let patched = match !patchFile with

    | Some(pf) -> (
        (* save old value of out so I can use it for debugging during patching *)
        let oldOut = !out in

        (* reset out so we don't try to print the patch file to it *)
        out := None;

        (trace "patch" (dprintf "newpatching %s\n" fname));
        let result = (Stats.time "newpatch" (Patch.applyPatch pf) cabs) in

        if (!printPatchedFiles) then begin                              
          let outFname:string = fname ^ ".patched" in
          (trace "patch" (dprintf "printing patched version of %s to %s\n"
                                  fname outFname));
          let o = (open_out outFname) in
          (Cprint.printFile o result);
          (close_out o)
        end;

        (* restore out *)
        Cprint.flush ();
        out := oldOut;

        result
      )
    | None -> cabs
  in

  (* print it ... *)
  (match !out with
    Some o -> begin
      (trace "sm" (dprintf "writing the cabs output\n"));
      if !printNotice then output_string o ("/* Generated by Frontc */\n");
      Stats.time "printCABS" (Cprint.printFile o) patched;
      close_output ();
      raise CabsOnly
    end
  | None -> ());
  if !E.hadErrors then
    raise Parsing.Parse_error;

  (* and return the patched source *)
  patched
end

and clexer lexbuf =
    Clexer.clear_white ();
    Clexer.clear_lexeme ();
    let token = Clexer.initial lexbuf in
    let white = Clexer.get_white () in
    let cabsloc = Clexer.currentLoc () in
    let lexeme = Clexer.get_extra_lexeme () ^ Lexing.lexeme lexbuf in
    white,lexeme,token,cabsloc

(* just parse *)
and parse_to_cabs_inner (fname : string) =
  try
    if !E.verboseFlag then ignore (E.log "Frontc is parsing %s\n" fname);
    flush !E.logChannel;
    let lexbuf = Clexer.init fname in
    let cabs = Stats.time "parse" (Cparser.interpret (Whitetrack.wraplexer clexer)) lexbuf in
    Whitetrack.setFinalWhite (Clexer.get_white ());
    Clexer.finish ();
    (fname, cabs)
  with (Sys_error msg) -> begin
    ignore (E.log "Cannot open %s : %s\n" fname msg);
    Clexer.finish ();
    close_output ();
    raise (ParseError("Cannot open " ^ fname ^ ": " ^ msg ^ "\n"))
  end
  | Parsing.Parse_error -> begin
      ignore (E.log "Parsing error");
      Clexer.finish ();
      close_output ();
      raise (ParseError("Parse error"))
  end
  | e -> begin
      ignore (E.log "Caught %s while parsing\n" (Printexc.to_string e));
      Clexer.finish ();
      raise e
  end

  
(* print to safec.proto.h the prototypes of all functions that are defined *)
let printPrototypes ((fname, file) : Cabs.file) : unit =
begin
  (*ignore (E.log "file has %d defns\n" (List.length file));*)

  let chan = open_out "safec.proto.h" in
  ignore (fprintf chan "/* generated prototypes file, %d defs */\n" (List.length file));
  Whitetrack.setOutput  chan;

  let counter : int ref = ref 0 in

  let rec loop (d : Cabs.definition) = begin
    match d with
    | Cabs.FUNDEF(name, _, loc, _) -> (
        match name with
        | (_, (funcname, Cabs.PROTO(_,_,_), _, _)) -> (
            incr counter;          
            ignore (fprintf chan "\n/* %s from %s:%d */\n"
                                 funcname loc.Cabs.filename loc.Cabs.lineno);
            flush chan;
            Cprint.print_single_name name;
            Cprint.print_unescaped_string ";";
            Cprint.force_new_line ();
            Cprint.flush ()
          )
        | _ -> ()
      )

    | _ -> ()
  end in
  (List.iter loop file);

  ignore (fprintf chan "\n/* wrote %d prototypes */\n" !counter);
  close_out chan;
  ignore (E.log "printed %d prototypes from %d defns to safec.proto.h\n"
                !counter (List.length file))
end

let get_goblint_pp_vars cabs =
  
  let vars: string list ref = ref [] in
  
  let is_prefix s p = String.length s >= String.length p && String.sub s 0 (String.length p) = p in
  
  let visitor = object
    inherit Cabsvisit.nopCabsVisitor as super
    
    method vstmt (s: Cabs.statement) = 
      begin match s with
      | GOBLINT_PP_IFELSE (v, _, _, _) when is_prefix v "GOBLINT_PP_VAR__" && not (List.exists (fun x -> x = v) (!vars)) -> 
        vars := v :: !vars;
      | _ -> ()
      end;
     super#vstmt s 
      
  end in
  
  let _ = Cabsvisit.visitCabsFile visitor cabs in
  List.rev (!vars)
  
let add_goblint_pp_vars_init cabs ppvars =
  
  let visitor = object
    inherit Cabsvisit.nopCabsVisitor as super
    
    method vdef (d: Cabs.definition) =
      let open Cabs in 
      let d' = 
        begin match d with
        | FUNDEF((_, ("main", _, _, _)) as n, block, l1, l2) -> 
          let loc = { lineno = 1; filename = "GOBLINT_PP_CODE"; byteno = 0; ident = 0 } in
          let mk_stmt v = COMPUTATION (BINARY (ASSIGN, VARIABLE v, CALL (VARIABLE "GOBLINT_PP_FUN__INIT_FLAG", [])), loc) in
          let stmts = List.map mk_stmt ppvars in
          let block' = { blabels = block.blabels; battrs = block.battrs; bstmts = stmts @ block.bstmts } in
          FUNDEF(n, block', l1, l2)
        | _ -> d
        end
      in
      ChangeTo [d']
      
  end in
  
  Cabsvisit.visitCabsFile visitor cabs

let add_goblint_pp_code cabss =
  
  let open Cabs in
  
  let ppvars = get_goblint_pp_vars cabss in
  List.iter print_endline ppvars;
  let loc = { lineno = 1; filename = "GOBLINT_PP_CODE"; byteno = 0; ident = 0 } in
  
  (* Definitions for pp variable initializing function. *)
  (* int GOBLINT_PP_FUN__INIT_FLAG () { int i; return !!i; } *)
  let pp_init_fun = 
    let stmt1 = DEFINITION (DECDEF (([SpecType Tint], [(("i", JUSTBASE, [], loc), NO_INIT)]), loc)) in
    let stmt2 = RETURN (UNARY (NOT, UNARY (NOT, VARIABLE "i")), loc) in
    let block = { blabels = []; battrs = []; bstmts = [stmt1; stmt2] } in
    let name = ("GOBLINT_PP_FUN__INIT_FLAG", PROTO (JUSTBASE, [] , false), [], loc) in
    FUNDEF (([SpecType Tint], name), block, loc, loc)
  in
  
  (* Definitions for pp variables. *)
  (* int GOBLINT_PP_VAR__XXX ; *)
  let pp_var_def v = DECDEF (([SpecType Tint], [((v, JUSTBASE, [], loc), NO_INIT)]), loc) in
  let pp_var_defs = List.map pp_var_def ppvars in
  
  let (cabs_s, cabs_ds) = cabss in
  let with_header = (cabs_s, pp_init_fun :: pp_var_defs @ cabs_ds) in
  
  add_goblint_pp_vars_init with_header ppvars

let parse_helper fname =
  (trace "sm" (dprintf "parsing %s to Cabs\n" fname));
  let cabs = parse_to_cabs fname in
  let cabs' = add_goblint_pp_code cabs in
  (* Now (return a function that will) convert to CIL *)
  fun _ ->
    (trace "sm" (dprintf "converting %s from Cabs to CIL\n" fname));
    let cil = Stats.time "convert to CIL" Cabs2cil.convFile cabs' in
    if !doPrintProtos then (printPrototypes cabs);
    cabs, cil

let parse fname = (fun () -> snd(parse_helper fname ()))

let parse_with_cabs fname = (fun () -> parse_helper fname ())
