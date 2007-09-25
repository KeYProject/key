resource myTypesOCL = open Prelude, precedenceOCL in {

--# -path=.:../prelude

lintype
    ClassL = {s : Str};
    Inst = {s0, s1 : Str; p : Prec; isAtpre : Bool};
    ConstraintL = {s: Str};
    DocumentL = {s : Str};    
    ArgList = {s : Str; empty : Bool};
    LetDefL = {
        s0 : Str; -- definiendum
        s1 : Str  -- definiens
    };
    LetDefListL = {s : Str; size : ENumber};
};
