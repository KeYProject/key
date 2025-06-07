parser grammar KeYSequentParser;

import KeYTermParser;

options { tokenVocab = KeYLexer; }
seq
   : ant = semisequent SEQARROW suc = semisequent
   ;

seqEOF
   : seq EOF
   ;

termorseq
   : head = term (COMMA s = seq | SEQARROW ss = semisequent)?
   | SEQARROW ss = semisequent
   ;

semisequent
   :
/* empty */
   
   | head = term (COMMA ss = semisequent)?
   ;

