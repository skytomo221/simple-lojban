// camxes.js.peg
// Copyright (c) 2013, 2014 Masato Hagiwara
// https://github.com/mhagiwara/camxes.js
//
// camxes.js can be used, modified, and re-distributed under MIT license.
// See LICENSE for the details.

// This is a Parsing Expression Grammar for Lojban.
// See http://bford.info/packrat/
//
// All rules have the form:
//
//     name = peg_expression
//
// which means that the grammatical construct "name" is parsed using
// "peg_expression".
//
// 1)  Names in lower case are grammatical constructs.
// 2)  Names in UPPER CASE are selma'o (lexeme) names, and are terminals.
// 3)  Concatenation is expressed by juxtaposition with no operator symbol.
// 4)  / represents *ORDERED* alternation (choice).  If the first
//     option succeeds, the others will never be checked.
// 5)  ? indicates that the element to the left is optional.
// 6)  * represents optional repetition of the construct to the left.
// 7)  + represents one_or_more repetition of the construct to the left.
// 8)  () serves to indicate the grouping of the other operators.
//
// Longest match wins.

// How to compile using Node.js: (Added by Masato Hagiwara)

// // load peg.js and the file system module
// > var PEG = require("pegjs")
// > var fs = require("fs")
// // read peg and build a parser
// > var camxes_peg = fs.readFileSync("/path/to/camxes.js.peg").toString();
// > var camxes = PEG.buildParser(camxes_peg, {cache: true});
// // test it
// > camxes.parse("ko'a broda");
// [ 'text',
//   [ 'text_1',
//     [ 'paragraphs', [Object] ] ] ]
// // write to a file
// > fs.writeFileSync("/path/to/camxes.js", camxes.toSource());


// ___ GRAMMAR ___



// ================================================================== //

/*
 *  PEGJS INITIALIZATION CODE
 */

{
  var _g_zoi_delim;

  function _join(arg) {
    if (typeof(arg) == "string")
      return arg;
    else if (arg) {
      var ret = "";
      for (var v in arg) { if (arg[v]) ret += _join(arg[v]); }
      return ret;
    }
  }

  function _node_empty(label, arg) {
    var ret = [];
    if (label) ret.push(label);
    if (arg && typeof arg == "object" && typeof arg[0] == "string" && arg[0]) {
      ret.push( arg );
      return ret;
    }
    if (!arg)
    {
      return ret;
    }
    return _node_int(label, arg);
  }

  function _node_int(label, arg) {
    if (typeof arg == "string")
      return arg;
    if (!arg) arg = [];
    var ret = [];
    if (label) ret.push(label);
    for (var v in arg) {
      if (arg[v] && arg[v].length != 0)
        ret.push( _node_int( null, arg[v] ) );
    }
    return ret;
  }

  function _node2(label, arg1, arg2) {
    return [label].concat(_node_empty(arg1)).concat(_node_empty(arg2));
  }

  function _node(label, arg) {
    var _n = _node_empty(label, arg);
    return (_n.length == 1 && label) ? [] : _n;
  }
  var _node_nonempty = _node;

  // === Functions for faking left recursion === //

  function _flatten_node(a) {
    // Flatten nameless nodes
    // e.g. [Name1, [[Name2, X], [Name3, Y]]] --> [Name1, [Name2, X], [Name3, Y]]
    if (is_array(a)) {
      var i = 0;
      while (i < a.length) {
        if (!is_array(a[i])) i++;
        else if (a[i].length === 0) // Removing []s
          a = a.slice(0, i).concat(a.slice(i + 1));
        else if (is_array(a[i][0]))
          a = a.slice(0, i).concat(a[i], a.slice(i + 1));
        else i++;
      }
    }
    return a;
  }

  function _group_leftwise(arr) {
    if (!is_array(arr)) return [];
    else if (arr.length <= 2) return arr;
    else return [_group_leftwise(arr.slice(0, -1)), arr[arr.length - 1]];
  }

  // "_lg" for "Leftwise Grouping".
  function _node_lg(label, arg) {
    return _node(label, _group_leftwise(_flatten_node(arg)));
  }

  function _node_lg2(label, arg) {
    if (is_array(arg) && arg.length == 2)
      arg = arg[0].concat(arg[1]);
    return _node(label, _group_leftwise(arg));
  }

  // === ZOI functions === //

  function _assign_zoi_delim(w) {
    if (is_array(w)) w = join_expr(w);
    else if (!is_string(w)) throw "ERROR: ZOI word is of type " + typeof w;
    w = w.toLowerCase().replace(/,/gm,"").replace(/h/g, "'");
    _g_zoi_delim = w;
    return;
  }

  function _is_zoi_delim(w) {
    if (is_array(w)) w = join_expr(w);
    else if (!is_string(w)) throw "ERROR: ZOI word is of type " + typeof w;
    /* Keeping spaces in the parse tree seems to result in the absorbtion of
       spaces into the closing delimiter candidate, so we'll remove any space
       character from our input. */
    w = w.replace(/[.\t\n\r?!\u0020]/g, "");
    w = w.toLowerCase().replace(/,/gm,"").replace(/h/g, "'");
    return w === _g_zoi_delim;
  }
	
	// === Stack functions === //

  _g_stack = []

  function _push(x) {
    if (is_array(x)) x = join_expr(x);
    else if (!is_string(x)) throw "Invalid argument type: " + typeof x;
    _g_stack.push(x);
    return;
  }

  function _pop() {
    return _g_stack.pop();
  }
	
	  function _peek() {
	  if (_g_stack.length <= 0) return null;
    else return _g_stack[_g_stack.length - 1];
  }
	
	_g_last_pred_val = null;
	
	function _pop_eq(x) {
    if (is_array(x)) x = join_expr(x);
    else if (!is_string(x)) throw "Invalid argument type: " + typeof x;
    /* Keeping spaces in the parse tree seems to result in the absorbtion of
       spaces into the closing delimiter candidate, so we'll remove any space
       character from our input. */
    x = x.replace(/[.\t\n\r?!\u0020]/g, "");
		l = _g_stack.length;
		y = _peek();
		r = x === y;
		_g_last_pred_val = r;
		if (r) _pop();
    return r;
  }
	
	function _peek_eq(x) {
    if (is_array(x)) x = join_expr(x);
    else if (!is_string(x)) throw "Invalid argument type: " + typeof x;
    /* Keeping spaces in the parse tree seems to result in the absorbtion of
       spaces into the closing delimiter candidate, so we'll remove any space
       character from our input. */
    x = x.replace(/[.\t\n\r?!\u0020]/g, "");
		l = _g_stack.length;
		y = _peek();
		r = x === y;
		_g_last_pred_val = r;
    return r;
  }

	// === MISC === //

  function join_expr(n) {
    if (!is_array(n) || n.length < 1) return "";
    var s = "";
    var i = is_array(n[0]) ? 0 : 1;
    while (i < n.length) {
      s += is_string(n[i]) ? n[i] : join_expr(n[i]);
      i++;
    }
    return s;
  }

  function is_string(v) {
    return Object.prototype.toString.call(v) === '[object String]';
  }

  function is_array(v) {
    return Object.prototype.toString.call(v) === '[object Array]';
  }
}

// ================================================================== //

text = expr:(intro_null NAI_clause* text_part_2 (!gek joik_jek)? text_1? EOF?) {return _node("text", expr);}

intro_null = expr:(initial_spaces?) {return _node("intro_null", expr);}

text_part_2 = expr:((CMEVLA_clause+ / indicators?) free*) {return _node("text_part_2", expr);}

// Please note that the "text_1" item in the text_1 production does
// *not* match the BNF. This is due to a bug in the BNF.  The change
// here was made to match grammar.300
text_1 = expr:(I_clause (jek / joik)? (stag? BO_clause)? free* text_1? / paragraphs) {return _node("text_1", expr);}

paragraphs = expr:(paragraph?) {return _node("paragraphs", expr);}

paragraph = expr:((statement / fragment) (I_clause !jek !joik !joik_jek free* (statement / fragment)?)*) {return _node("paragraph", expr);}

statement = expr:(statement_1 / prenex statement) {return _node("statement", expr);}

statement_1 = expr:(statement_2 (I_clause joik_jek statement_2?)*) {return _node("statement_1", expr);}

statement_2 = expr:(statement_3 (I_clause (jek / joik)? stag? BO_clause free* statement_2?)?) {return _node("statement_2", expr);}

statement_3 = expr:(sentence) {return _node("statement_3", expr);}

// BETA: NA sequence fragments
fragment = expr:(prenex / terms VAU_elidible free* / ek free* / gihek free* / quantifier / (NA_clause !JA_clause free*)+ / relative_clauses / links / linkargs) {return _node("fragment", expr);}

prenex = expr:(terms ZOhU_clause free*) {return _node("prenex", expr);}

//; sentence = (terms CU_clause? free*)? bridi_tail / bridi_tail

// BETA: JACU, JE.I
sentence = expr:(terms? bridi_tail_t1 (joik_jek bridi_tail / joik_jek stag? KE_clause free* bridi_tail KEhE_elidible free*)* (joik_jek I_clause free* subsentence)*) {return _node("sentence", expr);}

// BETA: JACU
bridi_tail_t1 = expr:(bridi_tail_t2 (joik_jek stag? KE_clause free* bridi_tail KEhE_elidible free*)?) {return _node("bridi_tail_t1", expr);}

// BETA: JACU
bridi_tail_t2 = expr:(bridi_tail (joik_jek stag? BO_clause free* bridi_tail)?) {return _node("bridi_tail_t2", expr);}


sentence_start = expr:(I_pre) {return _node("sentence_start", expr);}

subsentence = expr:(sentence / prenex subsentence) {return _node("subsentence", expr);}

// BETA: JACU
bridi_tail = expr:(bridi_tail_1 ((gihek / joik_jek) stag? KE_clause free* bridi_tail KEhE_elidible free* tail_terms)?) {return _node("bridi_tail", expr);}

bridi_tail_start = expr:(ME_clause / NU_clause / NA_clause !KU_clause / NAhE_clause !BO_clause / selbri / tag bridi_tail_start / KE_clause bridi_tail_start / bridi_tail) {return _node("bridi_tail_start", expr);}

// BETA: JACU
bridi_tail_1 = expr:(bridi_tail_2 ((gihek / joik_jek) !(stag? BO_clause) !(stag? KE_clause) free* bridi_tail_2 tail_terms)*) {return _node_lg2("bridi_tail_1", expr);}

// BETA: JACU
bridi_tail_2 = expr:(CU_elidible free* bridi_tail_3 ((gihek / joik_jek) stag? BO_clause free* bridi_tail_2 tail_terms)?) {return _node("bridi_tail_2", expr);}

// BETA: JACU
bridi_tail_3 = expr:((terms CU_elidible)* selbri tail_terms / gek_sentence) {return _node("bridi_tail_3", expr);}

gek_sentence = expr:(gek subsentence gik subsentence tail_terms / tag* KE_clause free* gek_sentence KEhE_elidible free* / NA_clause free* gek_sentence) {return _node("gek_sentence", expr);}

tail_terms = expr:(terms? VAU_elidible free*) {return _node("tail_terms", expr);}

terms = expr:(terms_1+) {return _node("terms", expr);}

//; terms_1 = terms_2

//; terms_2 = term

terms_1 = expr:(terms_2) {return _node("terms_1", expr);}

terms_2 = expr:(term) {return _node("terms_2", expr);}

//;term = sumti / ( !gek (tag / FA_clause free*) (sumti / KU_elidible free*) ) / termset / NA_clause KU_clause free*

term = expr:(term_1) {return _node("term", expr);}

// BEGIN BETA: TERM JA TERM
term_1 = expr:(term_2 (joik_ek !tag_bo_ke_bridi_tail term_2)*) {return _node("term_1", expr);}

tag_bo_ke_bridi_tail = expr:(stag (BO_clause / KE_clause) CU_elidible free* (selbri / gek_sentence)) {return _node("tag_bo_ke_bridi_tail", expr);}

term_2 = expr:(term_3 (joik_ek? stag? BO_clause term_3)*) {return _node("term_2", expr);}

term_3 = expr:(sumti / tag_term / nontag_adverbial / termset) {return _node("term_3", expr);}

tag_term = expr:(!gek (tag !(!tag selbri) / FA_clause free*) (sumti / KU_elidible free*)) {return _node("tag_term", expr);}

nonabs_term = expr:(nonabs_term_1) {return _node("nonabs_term", expr);}

nonabs_term_1 = expr:(nonabs_term_2 (joik_ek !tag_bo_ke_bridi_tail term_2)*) {return _node("nonabs_term_1", expr);}

nonabs_term_2 = expr:(nonabs_term_3 (joik_ek? stag? BO_clause term_3)*) {return _node("nonabs_term_2", expr);}

nonabs_term_3 = expr:(sumti / nonabs_tag_term / nontag_adverbial / termset) {return _node("nonabs_term_3", expr);}

nonabs_tag_term = expr:(!gek (tag !(!tag selbri) / FA_clause free*) (sumti / KU_elidible free*)) {return _node("nonabs_tag_term", expr);}

nontag_adverbial = expr:(NA_clause free* KU_clause free*) {return _node("nontag_adverbial", expr);}
// END BETA: TERM JA TERM

term_start = expr:(term_1 / LA_clause / LE_clause / LI_clause / LU_clause / LAhE_clause / quantifier term_start / gek sumti gik / FA_clause / tag term_start) {return _node("term_start", expr);}

// BETA: KE-termset
termset = expr:(gek_termset / KE_clause terms KEhE_elidible) {return _node("termset", expr);}

gek_termset = expr:(gek terms_gik_terms) {return _node("gek_termset", expr);}

terms_gik_terms = expr:(nonabs_term (gik / terms_gik_terms) nonabs_term) {return _node("terms_gik_terms", expr);}

sumti = expr:(sumti_1) {return _node("sumti", expr);}

sumti_1 = expr:(sumti_2 (joik_ek stag? KE_clause free* sumti KEhE_elidible free*)?) {return _node("sumti_1", expr);}

sumti_2 = expr:(sumti_3 (joik_ek sumti_3)*) {return _node_lg2("sumti_2", expr);}

sumti_3 = expr:(sumti_4 (joik_ek stag? BO_clause free* sumti_3)?) {return _node("sumti_3", expr);}

sumti_4 = expr:(sumti_5 / gek sumti gik sumti_4) {return _node("sumti_4", expr);}

sumti_5 = expr:(quantifier? sumti_6 relative_clauses? / quantifier selbri KU_elidible free* relative_clauses?) {return _node("sumti_5", expr);}

// BETA: NAhE+SUMTI, LAhE+TERM
sumti_6 = expr:(ZO_clause free* / ZOI_clause free* / LOhU_clause free* / lerfu_string !MOI_clause BOI_elidible free* / LU_clause text LIhU_elidible free* / (LAhE_clause free* / NAhE_clause BO_clause? free*) (relative_clauses? sumti / term) LUhU_elidible free* / KOhA_clause free* / LA_clause free* relative_clauses? CMEVLA_clause+ free* / (LA_clause / LE_clause) free* sumti_tail KU_elidible free* / li_clause) {return _node("sumti_6", expr);}

li_clause = expr:(LI_clause free* mex LOhO_elidible free*) {return _node("li_clause", expr);}

sumti_tail = expr:((sumti_6 relative_clauses?)? sumti_tail_1 / relative_clauses sumti_tail_1) {return _node("sumti_tail", expr);}

sumti_tail_1 = expr:(selbri relative_clauses? / quantifier selbri relative_clauses? / quantifier sumti) {return _node("sumti_tail_1", expr);}

// BETA: JAPOI
relative_clauses = expr:(relative_clause (joik_jek free* relative_clause)* / gek relative_clauses gik relative_clauses) {return _node("relative_clauses", expr);}

//; relative_clause = GOI_clause free* term GEhU_clause? free* / NOI_clause free* subsentence KUhO_clause? free*

relative_clause = expr:(relative_clause_1) {return _node("relative_clause", expr);}

relative_clause_1 = expr:(GOI_clause free* nonabs_term GEhU_elidible free* / NOI_clause free* subsentence KUhO_elidible free*) {return _node("relative_clause_1", expr);}

relative_clause_start = expr:(GOI_clause / NOI_clause) {return _node("relative_clause_start", expr);}

selbri = expr:(tag? selbri_1) {return _node("selbri", expr);}

selbri_1 = expr:(selbri_2 / NA_clause free* selbri) {return _node("selbri_1", expr);}

selbri_2 = expr:(selbri_3 (CO_clause free* selbri_2)?) {return _node("selbri_2", expr);}

selbri_3 = expr:(selbri_4+) {return _node_lg("selbri_3", expr);}

selbri_4 = expr:(selbri_5 (joik_jek selbri_5 / joik stag? KE_clause free* selbri_3 KEhE_elidible free*)*) {return _node_lg2("selbri_4", expr);}

selbri_5 = expr:(selbri_6 ((jek / joik) stag? BO_clause free* selbri_5)?) {return _node("selbri_5", expr);}

selbri_6 = expr:(tanru_unit (BO_clause free* selbri_6)? / NAhE_clause? free* guhek selbri gik selbri_6) {return _node("selbri_6", expr);}

tanru_unit = expr:(tanru_unit_1) {return _node("tanru_unit", expr);}

tanru_unit_1 = expr:(tanru_unit_2 linkargs?) {return _node("tanru_unit_1", expr);}

// ** zei is part of BRIVLA_clause

// BETA: Bare MEX
tanru_unit_2 = expr:(BRIVLA_clause free* / GOhA_clause free* / KE_clause free* selbri_3 KEhE_elidible free* / ME_clause free* (sumti / lerfu_string) MEhU_elidible free* MOI_clause? free* / mex MOI_clause free* / SE_clause free* tanru_unit_2 / NAhE_clause free* tanru_unit_2 / NU_clause NAI_clause? free* (joik_jek NU_clause NAI_clause? free*)* subsentence KEI_elidible free*) {return _node("tanru_unit_2", expr);}

//; linkargs = BE_clause free* term links? BEhO_clause? free*

linkargs = expr:(linkargs_1) {return _node("linkargs", expr);}

linkargs_1 = expr:(BE_clause free* nonabs_term links? BEhO_elidible free*) {return _node("linkargs_1", expr);}



linkargs_start = expr:(BE_clause) {return _node("linkargs_start", expr);}

//; links = BEI_clause free* term links?

links = expr:(links_1) {return _node("links", expr);}

links_1 = expr:(BEI_clause free* nonabs_term links?) {return _node("links_1", expr);}



links_start = expr:(BEI_clause) {return _node("links_start", expr);}

// BEGIN BETA: MEX simplification
quantifier = expr:(!selbri !sumti_6 mex) {return _node("quantifier", expr);}

//;mex = mex_1 (operator mex_1)* / rp_clause

mex = expr:(mex_1 (operator mex_1)*) {return _node("mex", expr);}

mex_1 = expr:(mex_2 (operator stag? BO_clause free* mex_1)?) {return _node("mex_1", expr);}

mex_2 = expr:(number BOI_elidible free* / lerfu_string BOI_elidible free* / gek mex gik mex_2 / (LAhE_clause free* / NAhE_clause free* BO_clause? free*) mex LUhU_elidible free*) {return _node("mex_2", expr);}

// END BETA: MEX simplification

//; operator = operator_1 (joik_jek operator_1 / joik stag? KE_clause free* operator KEhE_clause? free*)*

operator = expr:(operator_0) {return _node("operator", expr);}

operator_0 = expr:(operator_1 (joik_jek operator_1 / joik stag? KE_clause free* operator KEhE_elidible free*)*) {return _node("operator_0", expr);}



operator_start = expr:(guhek / KE_clause / SE_clause? NAhE_clause) {return _node("operator_start", expr);}

// BETA: MEX simplification
operator_1 = expr:(guhek operator_1 gik operator_2 / operator_2 (jek / joik) stag? BO_clause free* operator_1 / operator_2) {return _node("operator_1", expr);}

operator_2 = expr:(mex_operator / KE_clause free* operator KEhE_elidible free*) {return _node("operator_2", expr);}

// BETA: MEX simplification
mex_operator = expr:(SE_clause free* mex_operator / NAhE_clause free* mex_operator / joik_jek free* / ek free*) {return _node("mex_operator", expr);}

//; operand = operand_1 (joik_ek stag? KE_clause free* operand KEhE_clause? free*)?

operand = expr:(operand_0) {return _node("operand", expr);}

operand_0 = expr:(operand_1 (joik_ek stag? KE_clause free* operand KEhE_elidible free*)?) {return _node("operand_0", expr);}



operand_start = expr:(quantifier / lerfu_word / gek / LAhE_clause / NAhE_clause) {return _node("operand_start", expr);}

operand_1 = expr:(operand_2 (joik_ek operand_2)*) {return _node("operand_1", expr);}

operand_2 = expr:(operand_3 (joik_ek stag? BO_clause free* operand_2)?) {return _node("operand_2", expr);}

// BETA: NAhE+SUMTI
operand_3 = expr:(quantifier / lerfu_string !MOI_clause BOI_elidible free* / gek operand gik operand_3 / (LAhE_clause free* / NAhE_clause BO_clause? free*) operand LUhU_elidible free*) {return _node("operand_3", expr);}

// BETA: MEX simplification
// FIXME: forethought mex not possible anymore without pe'o. BIhE_clause isn't referenced anymore.
number = expr:(PA_clause+) {return _node("number", expr);}

lerfu_string = expr:(lerfu_word (PA_clause / lerfu_word)*) {return _node("lerfu_string", expr);}

// ** BU clauses are part of BY_clause
lerfu_word = expr:(BY_clause) {return _node("lerfu_word", expr);}

ek = expr:(NA_clause? SE_clause? A_clause NAI_clause?) {return _node("ek", expr);}

//; gihek = NA_clause? SE_clause? GIhA_clause NAI_clause?
gihek = expr:(gihek_1) {return _node("gihek", expr);}

gihek_1 = expr:(NA_clause? SE_clause? GIhA_clause NAI_clause?) {return _node("gihek_1", expr);}



jek = expr:(NA_clause? SE_clause? JA_clause NAI_clause?) {return _node("jek", expr);}

joik = expr:(SE_clause? JOI_clause NAI_clause?) {return _node("joik", expr);}

//; joik_ek = joik free* / ek free*
joik_ek = expr:(joik_ek_1) {return _node("joik_ek", expr);}

// BETA: A/JA/JOI/VUhU Merger
joik_ek_1 = expr:(joik_jek) {return _node("joik_ek_1", expr);}



// BETA: A/JA/JOI/VUhU Merger
joik_jek = expr:(joik free* / ek free* / jek free*) {return _node("joik_jek", expr);}

// BETA: gaJA
gek = expr:(gak SE_clause? joik_jek / SE_clause? GA_clause free* / joik GI_clause free* / stag gik) {return _node("gek", expr);}

// BETA: gaJA
gak = expr:(ga_clause !gek free*) {return _node("gak", expr);}

// BETA: guJA
guhek = expr:(guk SE_clause? joik_jek) {return _node("guhek", expr);}

// BETA: guJA
guk = expr:(gu_clause !gek free*) {return _node("guk", expr);}

gik = expr:(GI_clause NAI_clause? free*) {return _node("gik", expr);}

tag = expr:(tense_modal (joik_jek tense_modal)*) {return _node("tag", expr);}

//stag = simple_tense_modal ((jek / joik) simple_tense_modal)*

// BETA: Tag simplification
stag = expr:(tense_modal (joik_jek tense_modal)*) {return _node("stag", expr);}

// BETA: Tag simplification (dependency: NAI ∈ indicator)
// FIXME: Cannot use bare MEX with ROI.
tense_modal = expr:(((NAhE_clause? SE_clause? (BAI_clause / ZI_clause / PU_clause / FAhA_clause / number ROI_clause / ZAhO_clause / FA_clause) free*)+)) {return _node("tense_modal", expr);}

free = expr:(vocative relative_clauses? selbri relative_clauses? DOhU_elidible / vocative relative_clauses? CMEVLA_clause+ free* relative_clauses? DOhU_elidible / vocative sumti? DOhU_elidible / mex_2 MAI_clause free*) {return _node("free", expr);}

vocative = expr:((COI_clause NAI_clause?)+) {return _node("vocative", expr);}

indicators = expr:(indicator+) {return _node("indicators", expr);}

// BETA: NAI ∈ indicator
indicator = expr:(((UI_clause / CAI_clause) NAI_clause? / NAI_clause) !BU_clause) {return _node("indicator", expr);}


// ****************
// Magic Words
// ****************

bu_clause = expr:(pre_clause bu_clause_no_pre) {return _node("bu_clause", expr);}
bu_clause_no_pre = expr:(pre_zei_bu BU_clause+ post_clause) {return _node_lg("bu_clause_no_pre", expr);}

bu_tail = expr:(BU_clause+) {return _node("bu_tail", expr);} // Obsolete: please use BU_clause+ instead for allowing later left-grouping faking.

pre_zei_bu = expr:(!ZOI_start !BU_clause any_word_pre) {return _node("pre_zei_bu", expr);}
// LOhU_pre / ZO_pre / ZOI_pre / !BU_clause any_word_pre

any_word_pre = expr:(BRIVLA_pre / CMAVO_pre / CMEVLA_pre) {return _node("any_word_pre", expr);}

dot_star = expr:(.*) {return ["dot_star", _join(expr)];}

// __ General Morphology Issues
//
// 1.  Spaces (including '.y') and UI are eaten *after* a word.
//
// 3.  BAhE is eaten *before* a word.

// Handling of what can go after a cmavo
post_clause = expr:(spaces? !BU_clause indicators*) {return _node("post_clause", expr);}

// pre_clause <- BAhE_clause*  #: LR
pre_clause =


// ___ ELIDIBLE TERMINATORS ___

BEhO_elidible = expr:(BEhO_clause?) {return (expr === "" || !expr) ? ["BEhO"] : _node_empty("BEhO_elidible", expr);}
BOI_elidible = expr:(BOI_clause?) {return (expr === "" || !expr) ? ["BOI"] : _node_empty("BOI_elidible", expr);}
CU_elidible = expr:(CU_clause?) {return (expr === "" || !expr) ? ["CU"] : _node_empty("CU_elidible", expr);}
DOhU_elidible = expr:(DOhU_clause?) {return (expr === "" || !expr) ? ["DOhU"] : _node_empty("DOhU_elidible", expr);}
// FOI and FUhO are never elidible
GEhU_elidible = expr:(GEhU_clause?) {return (expr === "" || !expr) ? ["GEhU"] : _node_empty("GEhU_elidible", expr);}
KEI_elidible = expr:(KEI_clause?) {return (expr === "" || !expr) ? ["KEI"] : _node_empty("KEI_elidible", expr);}
KEhE_elidible = expr:(KEhE_clause?) {return (expr === "" || !expr) ? ["KEhE"] : _node_empty("KEhE_elidible", expr);}
KU_elidible = expr:(KU_clause?) {return (expr === "" || !expr) ? ["KU"] : _node_empty("KU_elidible", expr);}
KUhO_elidible = expr:(KUhO_clause?) {return (expr === "" || !expr) ? ["KUhO"] : _node_empty("KUhO_elidible", expr);}
// LEhU is never elidible
LIhU_elidible = expr:(LIhU_clause?) {return (expr === "" || !expr) ? ["LIhU"] : _node_empty("LIhU_elidible", expr);}
LOhO_elidible = expr:(LOhO_clause?) {return (expr === "" || !expr) ? ["LOhO"] : _node_empty("LOhO_elidible", expr);}
LUhU_elidible = expr:(LUhU_clause?) {return (expr === "" || !expr) ? ["LUhU"] : _node_empty("LUhU_elidible", expr);}
MEhU_elidible = expr:(MEhU_clause?) {return (expr === "" || !expr) ? ["MEhU"] : _node_empty("MEhU_elidible", expr);}
VAU_elidible = expr:(VAU_clause?) {return (expr === "" || !expr) ? ["VAU"] : _node_empty("VAU_elidible", expr);}


// ___ SELMAHO ___
// Do *NOT* delete the line above!

BRIVLA_clause = expr:(BRIVLA_pre BRIVLA_post) {return _node("BRIVLA_clause", expr);}
BRIVLA_pre = expr:(pre_clause BRIVLA spaces?) {return _node("BRIVLA_pre", expr);}
BRIVLA_post = expr:(post_clause) {return _node("BRIVLA_post", expr);}

CMEVLA_clause = expr:(CMEVLA_pre CMEVLA_post) {return _node("CMEVLA_clause", expr);}
CMEVLA_pre = expr:(pre_clause CMEVLA spaces?) {return _node("CMEVLA_pre", expr);}
CMEVLA_post = expr:(post_clause) {return _node("CMEVLA_post", expr);}

CMAVO_clause = expr:(CMAVO_pre CMAVO_post) {return _node("CMAVO_clause", expr);}
CMAVO_pre = expr:(pre_clause CMAVO spaces?) {return _node("CMAVO_pre", expr);}
CMAVO_post = expr:(post_clause) {return _node("CMAVO_post", expr);}

//         eks; basic afterthought logical connectives
A_clause = expr:(A_pre A_post) {return _node("A_clause", expr);}
A_pre = expr:(pre_clause A spaces?) {return _node("A_pre", expr);}
A_post = expr:(post_clause) {return _node("A_post", expr);}


//         modal operators
BAI_clause = expr:(BAI_pre BAI_post) {return _node("BAI_clause", expr);}
BAI_pre = expr:(pre_clause BAI spaces?) {return _node("BAI_pre", expr);}
BAI_post = expr:(post_clause) {return _node("BAI_post", expr);}

//         sumti link to attach sumti to a selbri
BE_clause = expr:(BE_pre BE_post) {return _node("BE_clause", expr);}
BE_pre = expr:(pre_clause BE spaces?) {return _node("BE_pre", expr);}
BE_post = expr:(post_clause) {return _node("BE_post", expr);}

//         multiple sumti separator between BE, BEI
BEI_clause = expr:(BEI_pre BEI_post) {return _node("BEI_clause", expr);}
BEI_pre = expr:(pre_clause BEI spaces?) {return _node("BEI_pre", expr);}
BEI_post = expr:(post_clause) {return _node("BEI_post", expr);}

//         terminates BEBEI specified descriptors
BEhO_clause = expr:(BEhO_pre BEhO_post) {return _node("BEhO_clause", expr);}
BEhO_pre = expr:(pre_clause BEhO spaces?) {return _node("BEhO_pre", expr);}
BEhO_post = expr:(post_clause) {return _node("BEhO_post", expr);}

//         joins two units with shortest scope
BO_clause = expr:(BO_pre BO_post) {return _node("BO_clause", expr);}
BO_pre = expr:(pre_clause BO spaces?) {return _node("BO_pre", expr);}
BO_post = expr:(post_clause) {return _node("BO_post", expr);}

//         number or lerfu_string terminator
BOI_clause = expr:(BOI_pre BOI_post) {return _node("BOI_clause", expr);}
BOI_pre = expr:(pre_clause BOI spaces?) {return _node("BOI_pre", expr);}
BOI_post = expr:(post_clause) {return _node("BOI_post", expr);}

//         turns any word into a BY lerfu word
BU_clause = expr:(BU_pre BU_post) {return _node("BU_clause", expr);}

BU_pre = expr:(pre_clause BU spaces?) {return _node("BU_pre", expr);}

BU_post = expr:(spaces?) {return _node("BU_post", expr);}

//         individual lerfu words
BY_clause = expr:(BY_pre BY_post / bu_clause) {return _node("BY_clause", expr);}
BY_pre = expr:(pre_clause BY spaces?) {return _node("BY_pre", expr);}
BY_post = expr:(post_clause) {return _node("BY_post", expr);}

//         afterthought intensity marker
CAI_clause = expr:(CAI_pre CAI_post) {return _node("CAI_clause", expr);}
CAI_pre = expr:(pre_clause CAI spaces?) {return _node("CAI_pre", expr);}
CAI_post = expr:(post_clause) {return _node("CAI_post", expr);}

//         tanru inversion
CO_clause = expr:(CO_pre CO_post) {return _node("CO_clause", expr);}
CO_pre = expr:(pre_clause CO spaces?) {return _node("CO_pre", expr);}
CO_post = expr:(post_clause) {return _node("CO_post", expr);}

COI_clause = expr:(COI_pre COI_post) {return _node("COI_clause", expr);}
COI_pre = expr:(pre_clause COI spaces?) {return _node("COI_pre", expr);}
COI_post = expr:(post_clause) {return _node("COI_post", expr);}

//         vocative marker permitted inside names; must
//         separator between head sumti and selbri
CU_clause = expr:(CU_pre CU_post) {return _node("CU_clause", expr);}
CU_pre = expr:(pre_clause CU spaces?) {return _node("CU_pre", expr);}
CU_post = expr:(post_clause) {return _node("CU_post", expr);}

//         terminator for DOI_marked vocatives
DOhU_clause = expr:(DOhU_pre DOhU_post) {return _node("DOhU_clause", expr);}
DOhU_pre = expr:(pre_clause DOhU spaces?) {return _node("DOhU_pre", expr);}
DOhU_post = expr:(post_clause) {return _node("DOhU_post", expr);}


//         modifier head generic case tag
FA_clause = expr:(FA_pre FA_post) {return _node("FA_clause", expr);}
FA_pre = expr:(pre_clause FA spaces?) {return _node("FA_pre", expr);}
FA_post = expr:(post_clause) {return _node("FA_post", expr);}

//         superdirections in space
FAhA_clause = expr:(FAhA_pre FAhA_post) {return _node("FAhA_clause", expr);}
FAhA_pre = expr:(pre_clause FAhA spaces?) {return _node("FAhA_pre", expr);}
FAhA_post = expr:(post_clause) {return _node("FAhA_post", expr);}


//         normally elided 'done pause' to indicate end
//                                    of utterance string

//         geks; forethought logical connectives
GA_clause = expr:(GA_pre GA_post) {return _node("GA_clause", expr);}
GA_pre = expr:(pre_clause GA spaces?) {return _node("GA_pre", expr);}
GA_post = expr:(post_clause) {return _node("GA_post", expr);}

//         marker ending GOI relative clauses
GEhU_clause = expr:(GEhU_pre GEhU_post) {return _node("GEhU_clause", expr);}
GEhU_pre = expr:(pre_clause GEhU spaces?) {return _node("GEhU_pre", expr);}
GEhU_post = expr:(post_clause) {return _node("GEhU_post", expr);}
// GEhU_no_SA_handling = pre_clause GEhU post_clause

//         forethought medial marker
GI_clause = expr:(GI_pre GI_post) {return _node("GI_clause", expr);}
GI_pre = expr:(pre_clause GI spaces?) {return _node("GI_pre", expr);}
GI_post = expr:(post_clause) {return _node("GI_post", expr);}

//         logical connectives for bridi_tails
GIhA_clause = expr:(GIhA_pre GIhA_post) {return _node("GIhA_clause", expr);}
GIhA_pre = expr:(pre_clause GIhA spaces?) {return _node("GIhA_pre", expr);}
GIhA_post = expr:(post_clause) {return _node("GIhA_post", expr);}

//         attaches a sumti modifier to a sumti
GOI_clause = expr:(GOI_pre GOI_post) {return _node("GOI_clause", expr);}
GOI_pre = expr:(pre_clause GOI spaces?) {return _node("GOI_pre", expr);}
GOI_post = expr:(post_clause) {return _node("GOI_post", expr);}

//         pro_bridi
GOhA_clause = expr:(GOhA_pre GOhA_post) {return _node("GOhA_clause", expr);}
GOhA_pre = expr:(pre_clause GOhA spaces?) {return _node("GOhA_pre", expr);}
GOhA_post = expr:(post_clause) {return _node("GOhA_post", expr);}

//         sentence link
I_clause = expr:(I_pre I_post) {return _node("I_clause", expr);}
I_pre = expr:(pre_clause I spaces?) {return _node("I_pre", expr);}
I_post = expr:(post_clause) {return _node("I_post", expr);}


//         jeks; logical connectives within tanru
JA_clause = expr:(JA_pre JA_post) {return _node("JA_clause", expr);}
JA_pre = expr:(pre_clause JA spaces?) {return _node("JA_pre", expr);}
JA_post = expr:(post_clause) {return _node("JA_post", expr);}

//         non_logical connectives
JOI_clause = expr:(JOI_pre JOI_post) {return _node("JOI_clause", expr);}
JOI_pre = expr:(pre_clause JOI spaces?) {return _node("JOI_pre", expr);}
JOI_post = expr:(post_clause) {return _node("JOI_post", expr);}


//         left long scope marker
KE_clause = expr:(KE_pre KE_post) {return _node("KE_clause", expr);}
KE_pre = expr:(pre_clause KE spaces?) {return _node("KE_pre", expr);}
KE_post = expr:(post_clause) {return _node("KE_post", expr);}

//         right terminator for KE groups
KEhE_clause = expr:(KEhE_pre KEhE_post) {return _node("KEhE_clause", expr);}
KEhE_pre = expr:(pre_clause KEhE spaces?) {return _node("KEhE_pre", expr);}
KEhE_post = expr:(post_clause) {return _node("KEhE_post", expr);}

//         right terminator, NU abstractions
KEI_clause = expr:(KEI_pre KEI_post) {return _node("KEI_clause", expr);}
KEI_pre = expr:(pre_clause KEI spaces?) {return _node("KEI_pre", expr);}
KEI_post = expr:(post_clause) {return _node("KEI_post", expr);}

//         sumti anaphora
KOhA_clause = expr:(KOhA_pre KOhA_post) {return _node("KOhA_clause", expr);}
KOhA_pre = expr:(pre_clause KOhA spaces?) {return _node("KOhA_pre", expr);}
KOhA_post = expr:(post_clause) {return _node("KOhA_post", expr);}

//         right terminator for descriptions, etc.
KU_clause = expr:(KU_pre KU_post) {return _node("KU_clause", expr);}
KU_pre = expr:(pre_clause KU spaces?) {return _node("KU_pre", expr);}
KU_post = expr:(post_clause) {return _node("KU_post", expr);}

//         right terminator, NOI relative clauses
KUhO_clause = expr:(KUhO_pre KUhO_post) {return _node("KUhO_clause", expr);}
KUhO_pre = expr:(pre_clause KUhO spaces?) {return _node("KUhO_pre", expr);}
KUhO_post = expr:(post_clause) {return _node("KUhO_post", expr);}


//         name descriptors
LA_clause = expr:(LA_pre LA_post) {return _node("LA_clause", expr);}
LA_pre = expr:(pre_clause LA spaces?) {return _node("LA_pre", expr);}
LA_post = expr:(post_clause) {return _node("LA_post", expr);}

//         sumti qualifiers
LAhE_clause = expr:(LAhE_pre LAhE_post) {return _node("LAhE_clause", expr);}
LAhE_pre = expr:(pre_clause LAhE spaces?) {return _node("LAhE_pre", expr);}
LAhE_post = expr:(post_clause) {return _node("LAhE_post", expr);}

//         sumti descriptors
LE_clause = expr:(LE_pre LE_post) {return _node("LE_clause", expr);}
LE_pre = expr:(pre_clause LE spaces?) {return _node("LE_pre", expr);}
LE_post = expr:(post_clause) {return _node("LE_post", expr);}


//         possibly ungrammatical text right quote
LEhU_clause = expr:(LEhU_pre LEhU_post) {return _node("LEhU_clause", expr);}
LEhU_pre = expr:(pre_clause LEhU spaces?) {return _node("LEhU_pre", expr);}
LEhU_post = expr:(spaces?) {return _node("LEhU_post", expr);}



//         convert number to sumti
LI_clause = expr:(LI_pre LI_post) {return _node("LI_clause", expr);}
LI_pre = expr:(pre_clause LI spaces?) {return _node("LI_pre", expr);}
LI_post = expr:(post_clause) {return _node("LI_post", expr);}

//         grammatical text right quote
LIhU_clause = expr:(LIhU_pre LIhU_post) {return _node("LIhU_clause", expr);}
LIhU_pre = expr:(pre_clause LIhU spaces?) {return _node("LIhU_pre", expr);}
LIhU_post = expr:(post_clause) {return _node("LIhU_post", expr);}

//         elidable terminator for LI
LOhO_clause = expr:(LOhO_pre LOhO_post) {return _node("LOhO_clause", expr);}
LOhO_pre = expr:(pre_clause LOhO spaces?) {return _node("LOhO_pre", expr);}
LOhO_post = expr:(post_clause) {return _node("LOhO_post", expr);}

//         possibly ungrammatical text left quote
LOhU_clause = expr:(LOhU_pre LOhU_post) {return _node("LOhU_clause", expr);}
LOhU_pre = expr:(pre_clause LOhU spaces? (!LEhU any_word)* LEhU_clause spaces?) {return _node("LOhU_pre", expr);}
LOhU_post = expr:(post_clause) {return _node("LOhU_post", expr);}

//         grammatical text left quote
LU_clause = expr:(LU_pre LU_post) {return _node("LU_clause", expr);}
LU_pre = expr:(pre_clause LU spaces?) {return _node("LU_pre", expr);}
LU_post = expr:(spaces? !BU_clause) {return _node("LU_post", expr);}
// LU_post isn't post_clause for avoiding indicators to attach to LU in the parse tree.

//         LAhE close delimiter
LUhU_clause = expr:(LUhU_pre LUhU_post) {return _node("LUhU_clause", expr);}
LUhU_pre = expr:(pre_clause LUhU spaces?) {return _node("LUhU_pre", expr);}
LUhU_post = expr:(post_clause) {return _node("LUhU_post", expr);}

//         change numbers to utterance ordinals
MAI_clause = expr:(MAI_pre MAI_post) {return _node("MAI_clause", expr);}
MAI_pre = expr:(pre_clause MAI spaces?) {return _node("MAI_pre", expr);}
MAI_post = expr:(post_clause) {return _node("MAI_post", expr);}

//         converts a sumti into a tanru_unit
ME_clause = expr:(ME_pre ME_post) {return _node("ME_clause", expr);}
ME_pre = expr:(pre_clause ME spaces?) {return _node("ME_pre", expr);}
ME_post = expr:(post_clause) {return _node("ME_post", expr);}

//         terminator for ME
MEhU_clause = expr:(MEhU_pre MEhU_post) {return _node("MEhU_clause", expr);}
MEhU_pre = expr:(pre_clause MEhU spaces?) {return _node("MEhU_pre", expr);}
MEhU_post = expr:(post_clause) {return _node("MEhU_post", expr);}

//         change number to selbri
MOI_clause = expr:(MOI_pre MOI_post) {return _node("MOI_clause", expr);}
MOI_pre = expr:(pre_clause MOI spaces?) {return _node("MOI_pre", expr);}
MOI_post = expr:(post_clause) {return _node("MOI_post", expr);}


//         bridi negation
NA_clause = expr:(NA_pre NA_post) {return _node("NA_clause", expr);}
NA_pre = expr:(pre_clause NA spaces?) {return _node("NA_pre", expr);}
NA_post = expr:(post_clause) {return _node("NA_post", expr);}

//         attached to words to negate them
NAI_clause = expr:(NAI_pre NAI_post) {return _node("NAI_clause", expr);}
NAI_pre = expr:(pre_clause NAI spaces?) {return _node("NAI_pre", expr);}
NAI_post = expr:(post_clause) {return _node("NAI_post", expr);}

//         scalar negation
NAhE_clause = expr:(NAhE_pre NAhE_post) {return _node("NAhE_clause", expr);}
NAhE_pre = expr:(pre_clause NAhE spaces?) {return _node("NAhE_pre", expr);}
NAhE_post = expr:(post_clause) {return _node("NAhE_post", expr);}

//         attaches a subordinate clause to a sumti
NOI_clause = expr:(NOI_pre NOI_post) {return _node("NOI_clause", expr);}
NOI_pre = expr:(pre_clause NOI spaces?) {return _node("NOI_pre", expr);}
NOI_post = expr:(post_clause) {return _node("NOI_post", expr);}

//         abstraction
NU_clause = expr:(NU_pre NU_post) {return _node("NU_clause", expr);}
NU_pre = expr:(pre_clause NU spaces?) {return _node("NU_pre", expr);}
NU_post = expr:(post_clause) {return _node("NU_post", expr);}

//         numbers and numeric punctuation
PA_clause = expr:(PA_pre PA_post) {return _node("PA_clause", expr);}
PA_pre = expr:(pre_clause PA spaces?) {return _node("PA_pre", expr);}
PA_post = expr:(post_clause) {return _node("PA_post", expr);}

//         directions in time
PU_clause = expr:(PU_pre PU_post) {return _node("PU_clause", expr);}
PU_pre = expr:(pre_clause PU spaces?) {return _node("PU_pre", expr);}
PU_post = expr:(post_clause) {return _node("PU_post", expr);}

//         converts number to extensional tense
ROI_clause = expr:(ROI_pre ROI_post) {return _node("ROI_clause", expr);}
ROI_pre = expr:(pre_clause ROI spaces?) {return _node("ROI_pre", expr);}
ROI_post = expr:(post_clause) {return _node("ROI_post", expr);}

//         metalinguistic eraser to the beginning of

//                                    the current utterance

//         conversions
SE_clause = expr:(SE_pre SE_post) {return _node("SE_clause", expr);}
SE_pre = expr:(pre_clause SE spaces?) {return _node("SE_pre", expr);}
SE_post = expr:(post_clause) {return _node("SE_post", expr);}

//         conversions
VAU_clause = expr:(VAU_pre VAU_post) {return _node("VAU_clause", expr);}
VAU_pre = expr:(pre_clause VAU spaces?) {return _node("VAU_pre", expr);}
VAU_post = expr:(post_clause) {return _node("VAU_post", expr);}

//         attitudinals, observationals, discursives
UI_clause = expr:(UI_pre UI_post) {return _node("UI_clause", expr);}
UI_pre = expr:(pre_clause UI spaces?) {return _node("UI_pre", expr);}
UI_post = expr:(post_clause) {return _node("UI_post", expr);}


//         event properties _ inchoative, etc.
ZAhO_clause = expr:(ZAhO_pre ZAhO_post) {return _node("ZAhO_clause", expr);}
ZAhO_pre = expr:(pre_clause ZAhO spaces?) {return _node("ZAhO_pre", expr);}
ZAhO_post = expr:(post_clause) {return _node("ZAhO_post", expr);}

//         time distance tense
ZI_clause = expr:(ZI_pre ZI_post) {return _node("ZI_clause", expr);}
ZI_pre = expr:(pre_clause ZI spaces?) {return _node("ZI_pre", expr);}
ZI_post = expr:(post_clause) {return _node("ZI_post", expr);}

//         single word metalinguistic quote marker
ZO_clause = expr:(ZO_pre ZO_post) {return _node("ZO_clause", expr);}
ZO_pre = expr:(pre_clause ZO spaces? any_word spaces?) {return _node("ZO_pre", expr);}
ZO_post = expr:(post_clause) {return _node("ZO_post", expr);}

//         delimited quote marker
ZOI_clause = expr:(ZOI_pre ZOI_post) {return _node("ZOI_clause", expr);}
ZOI_pre = expr:(pre_clause ZOI spaces? zoi_open spaces? (zoi_word spaces)* zoi_close spaces?) {return _node("ZOI_pre", expr);}
ZOI_post = expr:(post_clause) {return _node("ZOI_post", expr);}
ZOI_start = expr:(!ZOI_pre ZOI) {return _node("ZOI_start", expr);}

//         prenex terminator (not elidable)
ZOhU_clause = expr:(ZOhU_pre ZOhU_post) {return _node("ZOhU_clause", expr);}
ZOhU_pre = expr:(pre_clause ZOhU spaces?) {return _node("ZOhU_pre", expr);}
ZOhU_post = expr:(post_clause) {return _node("ZOhU_post", expr);}

// BEGIN BETA: gaJA, guJA
ga_clause = expr:(ga_pre ga_post) {return _node("ga_clause", expr);}
ga_pre = expr:(pre_clause ga_word spaces?) {return _node("ga_pre", expr);}
ga_post = expr:(post_clause) {return _node("ga_post", expr);}
ga_word = expr:(&cmavo ( g a ) &post_word) {return _node("ga_word", expr);}

gu_clause = expr:(gu_pre gu_post) {return _node("gu_clause", expr);}
gu_pre = expr:(pre_clause gu_word spaces?) {return _node("gu_pre", expr);}
gu_post = expr:(post_clause) {return _node("gu_post", expr);}
gu_word = expr:(&cmavo ( g u ) &post_word) {return _node("gu_word", expr);}
// END BETA: gaJA, guJA



// ___ MORPHOLOGY ___

CMEVLA = expr:(cmevla) {return _node("CMEVLA", expr);}
BRIVLA = expr:(gismu / lujvo / fuhivla) {return _node("BRIVLA", expr);}

// BETA: ZOhOI
CMAVO = expr:(A / BAI / BE / BEI / BEhO / BO / BOI / BU / BY / CAI / CO / COI / CU / DOhU / FA / FAhA / GA / GEhU / GI / GIhA / GOI / GOhA / I / JA / JOI / KE / KEhE / KEI / KOhA / KU / KUhO / LA / LAhE / LE / LEhU / LI / LIhU / LOhO / LOhU / LU / LUhU / MAI / ME / MEhU / MOI / NA / NAI / NAhE / NOI / NU / PA / PU / ROI / SE / VAU / UI / ZAhO / ZI / ZO / ZOI) {return _node("CMAVO", expr);}

// This is a Parsing Expression Grammar for the morphology of Lojban.
// See http://www.pdos.lcs.mit.edu/~baford/packrat/
//
// All rules have the form
//
// name = peg_expression
//
// which means that the grammatical construct "name" is parsed using
// "peg_expression".
//
// 1) Concatenation is expressed by juxtaposition with no operator symbol.
// 2) / represents *ORDERED* alternation (choice). If the first
// option succeeds, the others will never be checked.
// 3) ? indicates that the element to the left is optional.
// 4) * represents optional repetition of the construct to the left.
// 5) + represents one_or_more repetition of the construct to the left.
// 6) () serves to indicate the grouping of the other operators.
// 7) & indicates that the element to the right must follow (but the
// marked element itself does not absorb anything).
// 8) ! indicates that the element to the right must not follow (the
// marked element itself does not absorb anything).
// 9) . represents any character.
// 10) ' ' or " " represents a literal string.
// 11) [] represents a character class.
//
// Repetitions grab as much as they can.
//
//
// ___ GRAMMAR ___
// This grammar classifies words by their morphological class (cmevla,
// gismu, lujvo, fuhivla, cmavo, and non_lojban_word).
//
//The final section sorts cmavo into grammatical classes (A, BAI, ..., ZOhU).
//
// mi'e ((xorxes))

//___________________________________________________________________

// words = expr:(pause? (word pause?)*) { return _join(expr); }

// word = expr:lojban_word / non_lojban_word { return expr; }

// lojban_word = expr:(cmevla / cmavo / brivla) { return expr; }
lojban_word = expr:(CMEVLA / CMAVO / BRIVLA) {return _node("lojban_word", expr);}

any_word = expr:(lojban_word spaces?) {return _node("any_word", expr);}

// === ZOI quote handling ===

// Pure PEG cannot handle ZOI quotes, because it cannot check whether the closing
// delimiter is the same as the opening one.
// ZOI quote handling is the only part of Lojban's grammar that needs mechanisms
// external to the pure PEG grammar to be implemented properly; those mechanisms
// are implementation-specific.

zoi_open = expr:(lojban_word) { _push(expr); return _node("zoi_open", expr); }
// Non-PEG: Remember the value matched by this zoi_open.

zoi_word_2 = expr:(non_space+) {return ["zoi_word_2", _join(expr)];}

zoi_word = expr:(zoi_word_2) !{ return _peek_eq(expr); } { return _node("zoi_word", expr); }
// Non-PEG: Match successfully only if different from the most recent zoi_open.

zoi_close = expr:(any_word) &{ return _peek_eq(expr); } { if (_g_last_pred_val) _pop(); return _node("zoi_close", expr); }
// Non-PEG: Match successfully only if identical to the most recent zoi_open.

// BETA: ZOhOI
zohoi_word = expr:(non_space+) {return _node("zohoi_word", expr);}

//___________________________________________________________________

cmevla = expr:(jbocme / zifcme) {return _node("cmevla", expr);}

zifcme = expr:(!h (nucleus / glide / h / consonant !pause / digit)* consonant &pause) {return _node("zifcme", expr);}

jbocme = expr:(&zifcme (any_syllable / digit)+ &pause) {return _node("jbocme", expr);}

//cmevla = !h cmevla_syllable* &consonant coda? consonantal_syllable* onset &pause

//cmevla_syllable = !doi_la_lai_lahi coda? consonantal_syllable* onset nucleus / digit

//doi_la_lai_lahi = (d o i / l a (h? i)?) !h !nucleus

//___________________________________________________________________

cmavo = expr:(!cmevla !CVCy_lujvo cmavo_form &post_word) {return _node("cmavo", expr);}

CVCy_lujvo = expr:(CVC_rafsi y h? initial_rafsi* brivla_core / stressed_CVC_rafsi y short_final_rafsi) {return _node("CVCy_lujvo", expr);}

cmavo_form = expr:(!h !cluster onset (nucleus h)* (!stressed nucleus / nucleus !cluster) / y+ / digit) {return _node("cmavo_form", expr);}

//___________________________________________________________________

brivla = expr:(!cmavo initial_rafsi* brivla_core) {return _node("brivla", expr);}

brivla_core = expr:(fuhivla / gismu / CVV_final_rafsi / stressed_initial_rafsi short_final_rafsi) {return _node("brivla_core", expr);}

stressed_initial_rafsi = expr:(stressed_extended_rafsi / stressed_y_rafsi / stressed_y_less_rafsi) {return _node("stressed_initial_rafsi", expr);}

initial_rafsi = expr:(extended_rafsi / y_rafsi / !any_extended_rafsi y_less_rafsi !any_extended_rafsi) {return _node("initial_rafsi", expr);}

//___________________________________________________________________

any_extended_rafsi = expr:(fuhivla / extended_rafsi / stressed_extended_rafsi) {return _node("any_extended_rafsi", expr);}

fuhivla = expr:(fuhivla_head stressed_syllable consonantal_syllable* final_syllable) {return _node("fuhivla", expr);}

stressed_extended_rafsi = expr:(stressed_brivla_rafsi / stressed_fuhivla_rafsi) {return _node("stressed_extended_rafsi", expr);}

extended_rafsi = expr:(brivla_rafsi / fuhivla_rafsi) {return _node("extended_rafsi", expr);}

stressed_brivla_rafsi = expr:(&unstressed_syllable brivla_head stressed_syllable h y) {return _node("stressed_brivla_rafsi", expr);}

brivla_rafsi = expr:(&(syllable consonantal_syllable* syllable) brivla_head h y h?) {return _node("brivla_rafsi", expr);}

stressed_fuhivla_rafsi = expr:(fuhivla_head stressed_syllable consonantal_syllable* !h onset y) {return _node("stressed_fuhivla_rafsi", expr);}

fuhivla_rafsi = expr:(&unstressed_syllable fuhivla_head !h onset y h?) {return _node("fuhivla_rafsi", expr);}

fuhivla_head = expr:(!rafsi_string brivla_head) {return _node("fuhivla_head", expr);}

brivla_head = expr:(!cmavo !slinkuhi !h &onset unstressed_syllable*) {return _node("brivla_head", expr);}

slinkuhi = expr:(!rafsi_string consonant rafsi_string) {return _node("slinkuhi", expr);}

rafsi_string = expr:(y_less_rafsi* (gismu / CVV_final_rafsi / stressed_y_less_rafsi short_final_rafsi / y_rafsi / stressed_y_rafsi / stressed_y_less_rafsi? initial_pair y / hy_rafsi / stressed_hy_rafsi)) {return _node("rafsi_string", expr);}

//___________________________________________________________________

gismu = expr:((initial_pair stressed_vowel / consonant stressed_vowel consonant) &final_syllable consonant vowel &post_word) {return _node("gismu", expr);}

CVV_final_rafsi = expr:(consonant stressed_vowel h &final_syllable vowel &post_word) {return _node("CVV_final_rafsi", expr);}

short_final_rafsi = expr:(&final_syllable (consonant diphthong / initial_pair vowel) &post_word) {return _node("short_final_rafsi", expr);}

stressed_y_rafsi = expr:((stressed_long_rafsi / stressed_CVC_rafsi) y) {return _node("stressed_y_rafsi", expr);}

stressed_y_less_rafsi = expr:(stressed_CVC_rafsi !y / stressed_CCV_rafsi / stressed_CVV_rafsi) {return _node("stressed_y_less_rafsi", expr);}

stressed_long_rafsi = expr:(initial_pair stressed_vowel consonant / consonant stressed_vowel consonant consonant) {return _node("stressed_long_rafsi", expr);}

stressed_CVC_rafsi = expr:(consonant stressed_vowel consonant) {return _node("stressed_CVC_rafsi", expr);}

stressed_CCV_rafsi = expr:(initial_pair stressed_vowel) {return _node("stressed_CCV_rafsi", expr);}

stressed_CVV_rafsi = expr:(consonant (unstressed_vowel h stressed_vowel / stressed_diphthong) r_hyphen?) {return _node("stressed_CVV_rafsi", expr);}

y_rafsi = expr:((long_rafsi / CVC_rafsi) y h?) {return _node("y_rafsi", expr);}

y_less_rafsi = expr:(!y_rafsi !stressed_y_rafsi !hy_rafsi !stressed_hy_rafsi (CVC_rafsi / CCV_rafsi / CVV_rafsi) !h) {return _node("y_less_rafsi", expr);}

hy_rafsi = expr:((long_rafsi vowel / CCV_rafsi / CVV_rafsi) h y h?) {return _node("hy_rafsi", expr);}

stressed_hy_rafsi = expr:((long_rafsi stressed_vowel / stressed_CCV_rafsi / stressed_CVV_rafsi) h y) {return _node("stressed_hy_rafsi", expr);}

long_rafsi = expr:(initial_pair unstressed_vowel consonant / consonant unstressed_vowel consonant consonant) {return _node("long_rafsi", expr);}

CVC_rafsi = expr:(consonant unstressed_vowel consonant) {return _node("CVC_rafsi", expr);}

CCV_rafsi = expr:(initial_pair unstressed_vowel) {return _node("CCV_rafsi", expr);}

CVV_rafsi = expr:(consonant (unstressed_vowel h unstressed_vowel / unstressed_diphthong) r_hyphen?) {return _node("CVV_rafsi", expr);}

r_hyphen = expr:(r &consonant / n &r) {return _node("r_hyphen", expr);}

//___________________________________________________________________

final_syllable = expr:(onset !y !stressed nucleus !cmevla &post_word) {return _node("final_syllable", expr);}

stressed_syllable = expr:(&stressed syllable / syllable &stress) {return _node("stressed_syllable", expr);}

stressed_diphthong = expr:(&stressed diphthong / diphthong &stress) {return _node("stressed_diphthong", expr);}

stressed_vowel = expr:(&stressed vowel / vowel &stress) {return _node("stressed_vowel", expr);}

unstressed_syllable = expr:(!stressed syllable !stress / consonantal_syllable) {return _node("unstressed_syllable", expr);}

unstressed_diphthong = expr:(!stressed diphthong !stress) {return _node("unstressed_diphthong", expr);}

unstressed_vowel = expr:(!stressed vowel !stress) {return _node("unstressed_vowel", expr);}

//// FIX: Xorxes' fix for fu'ivla rafsi stress
stress = expr:((consonant / glide)* h? y? syllable pause) {return _node("stress", expr);}

stressed = expr:(onset comma* [AEIOU]) {return _node("stressed", expr);}

any_syllable = expr:(onset nucleus coda? / consonantal_syllable) {return _node("any_syllable", expr);}

syllable = expr:(onset !y nucleus coda?) {return _node("syllable", expr);}

//// FIX: preventing {bla'ypre} from being a valid lujvo
consonantal_syllable = expr:(consonant &syllabic coda) {return _node("consonantal_syllable", expr);}

coda = expr:(!any_syllable consonant &any_syllable / syllabic? consonant? &pause) {return _node("coda", expr);}

onset = expr:(h / glide / initial) {return _node("onset", expr);}

nucleus = expr:(vowel / diphthong / y !nucleus) {return _node("nucleus", expr);}

//_________________________________________________________________

glide = expr:((i / u) &nucleus) {return _node("glide", expr);}

diphthong = expr:((a i !i / a u !u / e i !i / o i !i) !nucleus) {return _node("diphthong", expr);}

vowel = expr:((a / e / i / o / u) !nucleus) {return _node("vowel", expr);}

a = expr:(comma* [aA]) {return _node("a", expr);}

e = expr:(comma* [eE]) {return _node("e", expr);}

i = expr:(comma* [iI]) {return _node("i", expr);}

o = expr:(comma* [oO]) {return _node("o", expr);}

u = expr:(comma* [uU]) {return _node("u", expr);}

y = expr:(comma* [yY] !(!y nucleus)) {return _node("y", expr);}



//___________________________________________________________________

cluster = expr:(consonant consonant+) {return _node("cluster", expr);}

initial_pair = expr:(&initial consonant consonant !consonant) {return _node("initial_pair", expr);}

initial = expr:((affricate / sibilant? other? liquid?) !consonant !glide) {return _node("initial", expr);}

affricate = expr:(t c / t s / d j / d z) {return _node("affricate", expr);}

liquid = expr:(l / r) {return _node("liquid", expr);}

other = expr:(p / t !l / k / f / x / b / d !l / g / v / m / n !liquid) {return _node("other", expr);}

sibilant = expr:(c / s !x / (j / z) !n !liquid) {return _node("sibilant", expr);}

consonant = expr:(voiced / unvoiced / syllabic) {return _node("consonant", expr);}

syllabic = expr:(l / m / n / r) {return _node("syllabic", expr);}

voiced = expr:(b / d / g / j / v / z) {return _node("voiced", expr);}

unvoiced = expr:(c / f / k / p / s / t / x) {return _node("unvoiced", expr);}

l = expr:(comma* [lL] !h !glide !l) {return _node("l", expr);}

m = expr:(comma* [mM] !h !glide !m !z) {return _node("m", expr);}

n = expr:(comma* [nN] !h !glide !n !affricate) {return _node("n", expr);}

r = expr:(comma* [rR] !h !glide !r) {return _node("r", expr);}

b = expr:(comma* [bB] !h !glide !b !unvoiced) {return _node("b", expr);}

d = expr:(comma* [dD] !h !glide !d !unvoiced) {return _node("d", expr);}

g = expr:(comma* [gG] !h !glide !g !unvoiced) {return _node("g", expr);}

v = expr:(comma* [vV] !h !glide !v !unvoiced) {return _node("v", expr);}

j = expr:(comma* [jJ] !h !glide !j !z !unvoiced) {return _node("j", expr);}

z = expr:(comma* [zZ] !h !glide !z !j !unvoiced) {return _node("z", expr);}

s = expr:(comma* [sS] !h !glide !s !c !voiced) {return _node("s", expr);}

c = expr:(comma* [cC] !h !glide !c !s !x !voiced) {return _node("c", expr);}

x = expr:(comma* [xX] !h !glide !x !c !k !voiced) {return _node("x", expr);}

k = expr:(comma* [kK] !h !glide !k !x !voiced) {return _node("k", expr);}

f = expr:(comma* [fF] !h !glide !f !voiced) {return _node("f", expr);}

p = expr:(comma* [pP] !h !glide !p !voiced) {return _node("p", expr);}

t = expr:(comma* [tT] !h !glide !t !voiced) {return _node("t", expr);}

h = expr:(comma* ['h] &nucleus) {return _node("h", expr);}

//___________________________________________________________________

digit = expr:(comma* [0123456789] !h !nucleus) {return _node("digit", expr);}

post_word = expr:(pause / !nucleus lojban_word) {return _node("post_word", expr);}

pause = expr:(comma* space_char+ / EOF) {return _node("pause", expr);}

EOF = expr:(comma* !.) {return _node("EOF", expr);}

comma = expr:([,]) {return _node("comma", expr);}

// This is an orphan rule.
non_lojban_word = expr:(!lojban_word non_space+) {return _node("non_lojban_word", expr);}

non_space = expr:(!space_char .) {return _join(expr);}

//Unicode_style and escaped chars not compatible with cl_peg
space_char = expr:([.\t\n\r?!\u0020]) {return _join(expr);}

// space_char = [.?! ] / space_char1 / space_char2
// space_char1 = '    '
// space_char2 = ''

//___________________________________________________________________

spaces = expr:(initial_spaces) {return _node("spaces", expr);}

initial_spaces = expr:((comma* space_char)+ EOF? / EOF) {return ["initial_spaces", _join(expr)];}

ybu = expr:(Y space_char* BU) {return _node("ybu", expr);}

lujvo = expr:(!gismu !fuhivla brivla) {return _node("lujvo", expr);}

//___________________________________________________________________

A = expr:(&cmavo ( a / e / j i / o / u ) &post_word) {return _node("A", expr);}

BAI = expr:(&cmavo ( d u h o / s i h u / z a u / k i h i / d u h i / c u h u / t u h i / t i h u / d i h o / j i h u / r i h a / n i h i / m u h i / k i h u / v a h u / k o i / c a h i / t a h i / p u h e / j a h i / k a i / b a i / f i h e / d e h i / c i h o / m a u / m u h u / r i h i / r a h i / k a h a / p a h u / p a h a / l e h a / k u h u / t a i / b a u / m a h i / c i h e / f a u / p o h i / c a u / m a h e / c i h u / r a h a / p u h a / l i h e / l a h u / b a h i / k a h i / s a u / f a h e / b e h i / t i h i / j a h e / g a h a / v a h o / j i h o / m e h a / d o h e / j i h e / p i h o / g a u / z u h e / m e h e / r a i ) &post_word) {return _node("BAI", expr);}

BE = expr:(&cmavo ( b e ) &post_word) {return _node("BE", expr);}

BEI = expr:(&cmavo ( b e i ) &post_word) {return _node("BEI", expr);}

BEhO = expr:(&cmavo ( b e h o ) &post_word) {return _node("BEhO", expr);}

BO = expr:(&cmavo ( b o ) &post_word) {return _node("BO", expr);}

BOI = expr:(&cmavo ( b o i ) &post_word) {return _node("BOI", expr);}

BU = expr:(&cmavo ( b u ) &post_word) {return _node("BU", expr);}

// BETA: a'y, e'y, i'y, o'y, u'y, iy, uy
BY = expr:(&cmavo ( ybu / j o h o / r u h o / g e h o / j e h o / l o h a / n a h a / s e h e / t o h a / g a h e / y h y / a h y / e h y / i h y / o h y / u h y / i y / u y / b y / c y / d y / f y / g y / j y / k y / l y / m y / n y / p y / r y / s y / t y / v y / x y / z y ) &post_word) {return _node("BY", expr);}

CAI = expr:(&cmavo ( p e i / c a i / c u h i / s a i / r u h e ) &post_word) {return _node("CAI", expr);}

CO = expr:(&cmavo ( c o ) &post_word) {return _node("CO", expr);}

// BETA: di'ai, jo'au, co'oi, da'oi, ki'ai, sa'ei
COI = expr:(&cmavo ( d o i / d i h a i / j o h a u / c o h o i / d a h o i / k i h a i / s a h e i / j u h i / c o i / f i h i / t a h a / m u h o / f e h o / c o h o / p e h u / k e h o / n u h e / r e h i / b e h e / j e h e / m i h e / k i h e / v i h o ) &post_word) {return _node("COI", expr);}

CU = expr:(&cmavo ( c u ) &post_word) {return _node("CU", expr);}

DOhU = expr:(&cmavo ( d o h u ) &post_word) {return _node("DOhU", expr);}

FA = expr:(&cmavo ( f a i / f a / f e / f o / f u / f i h a / f i ) &post_word) {return _node("FA", expr);}

FAhA = expr:(&cmavo ( d u h a / b e h a / n e h u / v u h a / g a h u / t i h a / n i h a / c a h u / z u h a / r i h u / r u h u / r e h o / t e h e / b u h u / n e h a / p a h o / n e h i / t o h o / z o h i / z e h o / z o h a / f a h a ) &post_word &post_word) {return _node("FAhA", expr);}

GA = expr:(&cmavo ( g e h i / g e / g o / g a / g u ) &post_word) {return _node("GA", expr);}

GEhU = expr:(&cmavo ( g e h u ) &post_word) {return _node("GEhU", expr);}

GI = expr:(&cmavo ( g i ) &post_word) {return _node("GI", expr);}

GIhA = expr:(&cmavo ( g i h e / g i h i / g i h o / g i h a / g i h u ) &post_word) {return _node("GIhA", expr);}

GOI = expr:(&cmavo ( n o h u / n e / g o i / p o h u / p e / p o h e / p o ) &post_word) {return _node("GOI", expr);}

GOhA = expr:(&cmavo ( m o / n e i / g o h u / g o h o / g o h i / n o h a / g o h e / g o h a / d u / b u h a / b u h e / b u h i / c o h e ) &post_word) {return _node("GOhA", expr);}

I = expr:(&cmavo ( i ) &post_word) {return _node("I", expr);}

JA = expr:(&cmavo ( j e h i / j e / j o / j a / j u ) &post_word) {return _node("JA", expr);}

JOI = expr:(&cmavo ( f a h u / p i h u / j o i / c e h o / c e / j o h u / k u h a / j o h e / j u h e ) &post_word) {return _node("JOI", expr);}

KE = expr:(&cmavo ( k e ) &post_word) {return _node("KE", expr);}

KEhE = expr:(&cmavo ( k e h e ) &post_word) {return _node("KEhE", expr);}

KEI = expr:(&cmavo ( k e i ) &post_word) {return _node("KEI", expr);}

// BETA: xai, zu'ai
KOhA = expr:(&cmavo ( z u h a i / d a h u / d a h e / d i h u / d i h e / d e h u / d e h e / d e i / d o h i / m i h o / m a h a / m i h a / d o h o / k o h a / f o h u / k o h e / k o h i / k o h o / k o h u / f o h a / f o h e / f o h i / f o h o / v o h a / v o h e / v o h i / v o h o / v o h u / r u / r i / r a / t a / t u / t i / z i h o / k e h a / m a / z u h i / z o h e / c e h u / x a i / d a / d e / d i / k o / m i / d o ) &post_word) {return _node("KOhA", expr);}

KU = expr:(&cmavo ( k u ) &post_word) {return _node("KU", expr);}

KUhO = expr:(&cmavo ( k u h o ) &post_word) {return _node("KUhO", expr);}

// BETA: la'ei
LA = expr:(&cmavo ( l a h e i / l a i / l a h i / l a ) &post_word) {return _node("LA", expr);}

// BETA: zo'ei
LAhE = expr:(&cmavo ( z o h e i / t u h a / l u h a / l u h o / l a h e / v u h i / l u h i / l u h e ) &post_word) {return _node("LAhE", expr);}

// BETA: me'ei, mo'oi, ri'oi
LE = expr:(&cmavo ( m e h e i / m o h o i / r i h o i / l e i / l o i / l e h i / l o h i / l e h e / l o h e / l o / l e ) &post_word) {return _node("LE", expr);}

LEhU = expr:(&cmavo ( l e h u ) &post_word) {return _node("LEhU", expr);}

LI = expr:(&cmavo ( m e h o / l i ) &post_word) {return _node("LI", expr);}

LIhU = expr:(&cmavo ( l i h u ) &post_word) {return _node("LIhU", expr);}

LOhO = expr:(&cmavo ( l o h o ) &post_word) {return _node("LOhO", expr);}

LOhU = expr:(&cmavo ( l o h u ) &post_word) {return _node("LOhU", expr);}

// BETA: la'au
LU = expr:(&cmavo ( l a h a u / l u ) &post_word) {return _node("LU", expr);}

LUhU = expr:(&cmavo ( l u h u ) &post_word) {return _node("LUhU", expr);}

// BETA: ju'ai
MAI = expr:(&cmavo ( m o h o / m a i / j u h a i ) &post_word) {return _node("MAI", expr);}

// BETA: me'au
ME = expr:(&cmavo (m e h a u / m e) &post_word) {return _node("ME", expr);}

MEhU = expr:(&cmavo ( m e h u ) &post_word) {return _node("MEhU", expr);}

MOI = expr:(&cmavo ( m e i / m o i / s i h e / c u h o / v a h e ) &post_word) {return _node("MOI", expr);}

NA = expr:(&cmavo ( j a h a / n a ) &post_word) {return _node("NA", expr);}

// BETA: ja'ai
NAI = expr:(&cmavo ( n a i / j a h a i ) &post_word) {return _node("NAI", expr);}

NAhE = expr:(&cmavo ( t o h e / j e h a / n a h e / n o h e ) &post_word) {return _node("NAhE", expr);}

// BETA: ji'oi
NOI = expr:(&cmavo ( v o i / n o i / p o i ) &post_word) {return _node("NOI", expr);}

// BETA: poi'i, kai'u
NU = expr:(&cmavo ( p o i h i / k a i h u / n i / d u h u / s i h o / n u / l i h i / k a / j e i / s u h u / z u h o / m u h e / p u h u / z a h i ) &post_word) {return _node("NU", expr);}

// BETA: xo'e, su'oi, ro'oi
PA = expr:(&cmavo ( s u h o i / r o h o i / x o h e / d a u / f e i / g a i / j a u / r e i / v a i / p i h e / p i / f i h u / z a h u / m e h i / n i h u / k i h o / c e h i / m a h u / r a h e / d a h a / s o h a / j i h i / s u h o / s u h e / r o / r a u / s o h u / s o h i / s o h e / s o h o / m o h a / d u h e / t e h o / k a h o / c i h i / t u h o / x o / p a i / n o h o / n o / p a / r e / c i / v o / m u / x a / z e / b i / s o / digit ) &post_word) {return _node("PA", expr);}

PU = expr:(&cmavo ( b a / p u / c a ) &post_word) {return _node("PU", expr);}

// BETA: va'ei, mu'ei
ROI = expr:(&cmavo ( r e h u / r o i / v a h e i / m u h e i ) &post_word) {return _node("ROI", expr);}

SE = expr:(&cmavo ( s e / t e / v e / x e ) &post_word) {return _node("SE", expr);}

VAU = expr:(&cmavo ( v a u ) &post_word) {return _node("VAU", expr);}

// BETA: ko'oi, si'au, o'ai, xe'e, xo'o
UI = expr:(&cmavo ( k o h o i / s i h a u / a h o i / o h a i / x e h e / x o h o / i h a / i e / a h e / u h i / i h o / i h e / a h a / i a / o h i / o h e / e h e / o i / u o / e h i / u h o / a u / u a / a h i / i h u / i i / u h a / u i / a h o / a i / a h u / i u / e i / o h o / e h a / u u / o h a / o h u / u h u / e h o / i o / e h u / u e / i h i / u h e / b a h a / j a h o / c a h e / s u h a / t i h e / k a h u / s e h o / z a h a / p e h i / r u h a / j u h a / t a h o / r a h u / l i h a / b a h u / m u h a / d o h a / t o h u / v a h i / p a h e / z u h u / s a h e / l a h a / k e h u / s a h u / d a h i / j e h u / s a h a / k a u / t a h u / n a h i / j o h a / b i h u / l i h o / p a u / m i h u / k u h i / j i h a / s i h a / p o h o / p e h a / r o h i / r o h e / r o h o / r o h u / r o h a / r e h e / l e h o / j u h o / f u h i / d a i / g a h i / z o h o / b e h u / r i h e / s e h i / s e h a / v u h e / k i h a / x u / g e h e / b u h o ) &post_word) {return _node("UI", expr);}

Y = expr:(&cmavo ( y ) &post_word) {return _node("Y", expr);}

// BETA: xa'o
ZAhO = expr:(&cmavo ( c o h i / p u h o / c o h u / m o h u / c a h o / c o h a / d e h a / b a h o / d i h a / z a h o / x a h o ) &post_word) {return _node("ZAhO", expr);}

ZI = expr:(&cmavo ( z u / z a / z i ) &post_word) {return _node("ZI", expr);}

// BETA: ma'oi
ZO = expr:(&cmavo ( z o / m a h o i ) &post_word) {return _node("ZO", expr);}

ZOI = expr:(&cmavo ( z o i / l a h o ) &post_word) {return _node("ZOI", expr);}

// BETA: ce'ai
ZOhU = expr:(&cmavo ( c e h a i / z o h u ) &post_word) {return _node("ZOhU", expr);}

