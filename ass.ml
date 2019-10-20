(* Limitations: (1) no real parser; (2) no error handling; (3) a lot of other stuff. *)

open Core

(* helpers *)

let rec print_fmt_string_array a =
    match a with
    | h::tl -> printf "%s\n" h; print_fmt_string_array tl
    | [] -> print_string ""

let print_symbol_table st =
    Hashtbl.iteri st ~f:(fun ~key:k ~data:d -> printf "%s \t-> \t%d\n" k d)

let rec revbinl_of_int b =
    if b = 0 then [] else (string_of_int (b mod 2))::(revbinl_of_int (b/2))

let bins_of_int b =
    String.rev (String.concat ~sep:"" (revbinl_of_int b))

let bins15_of_int b =
    let bbin = bins_of_int b in
    String.concat [String.init (15 - (String.length bbin)) ~f:(fun _ -> '0'); bbin]

(* assembler *)

let cut_comment s =
    match (String.substr_index s ~pattern:"//") with
    | Some x -> String.sub s ~pos:0 ~len:x
    | None -> s

let process_string_clean s =
    (* remove comments and then whitespaces from a string s that doesn't contain newlines *) 
    let ncinstr = cut_comment s in
    let filtered_str_list = List.filter (String.split_on_chars ncinstr ~on:[' '; '\t']) ~f:(fun x -> (String.length x > 0)) in
    String.concat ~sep:"" filtered_str_list

let rec cleaning_pass a =
    (* remove all comments and whitespaces *)
    match a with
    | h::tl -> let hp = process_string_clean h in
        if String.length hp > 0 then hp :: (cleaning_pass tl) else cleaning_pass tl
    | [] -> []

let rec label_gathering_pass_r a st n =
    (* fill the symbol table st with line numbers for each encounter of jump label in a; the current line number is n*)
    match a with
    | h::tl -> if h.[0] = '(' then
                               begin
                               Hashtbl.add_exn st ~key:(String.slice h 1 (String.length h - 1)) ~data:(n);
                               label_gathering_pass_r tl st n
                               end
               else h::(label_gathering_pass_r tl st (n+1))
    | _ -> []
and label_gathering_pass a st =
    label_gathering_pass_r a st 0

let lookup_symbol st symb ctr =
    (* ctr is the next address to be assigned to a new pointer:
       lookup the symbol or allocate with increment-and-return of ctr *)
    match (Hashtbl.find st symb) with
    | Some x -> x
    | None -> begin
      	      Hashtbl.add_exn st ~key:(symb) ~data:(!ctr);
	      ctr := !ctr + 1; !ctr - 1
	      end

let rec symbol_substitution_pass a st ctr = 
    (* substitute all the symbols in a according to symbol table st using counter ctr *)
    match a with
    | h::tl -> if h.[0] = '@' then 
			      let symb = (String.slice h 1 (String.length h)) in 
                              let addr = try int_of_string symb with Failure _ -> (lookup_symbol st symb ctr) in
			      (String.concat ["@"; string_of_int addr])::(symbol_substitution_pass tl st ctr)
			      else h::(symbol_substitution_pass tl st ctr)
    | [] -> []

type c_instruction =
{
     mutable dest: string;
     mutable cmd: string;
     mutable jmp: string;
}
   
let fetch_C_instruction cinstr =
    let cinstr_r = {dest = ""; cmd = ""; jmp = ""} in
    let destsplit = String.split_on_chars cinstr ~on:['='] in
	let _ = match destsplit with
	| [hd]   -> cinstr_r.cmd <- hd; cinstr_r
	| [hd;tl] -> (cinstr_r.dest <- hd; cinstr_r.cmd <- tl; cinstr_r)
	| _     -> cinstr_r.cmd <- "ERR0"; cinstr_r (* should not happen *)
        in let jmpsplit = String.split_on_chars cinstr_r.cmd ~on:[';'] in
        match jmpsplit with
	| [_]   -> cinstr_r
	| [hd;tl] -> (cinstr_r.cmd <- hd; cinstr_r.jmp <- tl; cinstr_r)
	| _     -> cinstr_r.cmd <- "ERR1"; cinstr_r (* should not happen *)

let encode_C_instruction cinstr =
        (* decode comp; added some commutatinve variations because they are present in examples *)
    	let cmdbits =
	match cinstr.cmd with
	| "0"   -> "0101010"
	| "1"   -> "0111111"
	| "-1"  -> "0111010"
	| "D"   -> "0001100"
	| "A"   -> "0110000"
	| "!D"  -> "0001101"
	| "!A"  -> "0110001"
	| "-D"  -> "0001111"
	| "-A"  -> "0110011"
	| "D+1" -> "0011111"
	| "A+1" -> "0110111"
	| "D-1" -> "0001110"
	| "A-1" -> "0110010"
	| "D+A" -> "0000010"
	| "D-A" -> "0010011"
	| "A-D" -> "0000111"
	| "D&A" -> "0000000"
	| "D|A" -> "0010101"

	| "1+D" -> "0011111"
	| "1+A" -> "0110111"
	| "A+D" -> "0000010"
	| "A&D" -> "0000000"
	| "A|D" -> "0010101"
	
	| "M"   -> "1110000"
	| "!M"  -> "1110001"
	| "-M"  -> "1110011"
	| "M+1" -> "1110111"
	| "M-1" -> "1110010"
	| "D+M" -> "1000010"
	| "D-M" -> "1010011"
	| "M-D" -> "1000111"
	| "D&M" -> "1000000"
	| "D|M" -> "1010101"

	| "1+M" -> "1110111"
	| "M+D" -> "1000010"
	| "M&D" -> "1000000"
	| "M|D" -> "1010101"

	| _ -> "ERR2"
	in
	let destbits =
	match cinstr.dest with
	| "M"   -> "001"
	| "D"   -> "010"
	| "MD"  -> "011"
	| "A"   -> "100"
	| "AM"  -> "101"
	| "AD"  -> "110"
	| "AMD" -> "111"
	| ""    -> "000"
	| _     -> "ERR3"
	in
	let jmpbits =
	match cinstr.jmp with
	| "JGT" -> "001"
	| "JEQ" -> "010"
	| "JGE" -> "011"
	| "JLT" -> "100"
	| "JNE" -> "101"
	| "JLE" -> "110"
	| "JMP" -> "111"
	| ""    -> "000"
	| _     -> "ERR4"
	in String.concat ["111"; cmdbits; destbits; jmpbits]

let rec translation_pass a =
    (* translate to zeros and ones! *)
    match a with
    | h::tl -> if h.[0] = '@' then (* A-instructions *)
			      let vald = (String.slice h 1 (String.length h)) in
			      (String.concat ["0"; bins15_of_int (int_of_string vald)])::(translation_pass tl)
			      else (* C-instructions *) 
			      (encode_C_instruction (fetch_C_instruction h))::(translation_pass tl)
    | [] -> []

let fill_init_symbols st =
    let predef =
    	[|("SP", 0); ("LCL", 1); ("ARG", 2); ("THIS", 3);
	("THAT", 4); ("SCREEN", 16384); ("KBD", 24576)|]
    in
    for ctr = 0 to Array.length predef - 1 do
    Hashtbl.add_exn st ~key:(fst predef.(ctr)) ~data:(snd predef.(ctr))
    done;
    for ctr = 0 to 15 do
    Hashtbl.add_exn st ~key:(String.concat ["R"; string_of_int ctr]) ~data:(ctr)
    done

(* entry point *)
let (symbol_table : (string, int) Hashtbl.t) = (Hashtbl.create ~hashable:String.hashable ());;
fill_init_symbols symbol_table;
    let ctr = ref 16 in
    let filei = (In_channel.read_lines Sys.argv.(1)) in
            print_fmt_string_array (translation_pass (symbol_substitution_pass
					  (label_gathering_pass (cleaning_pass filei) symbol_table) symbol_table ctr))
