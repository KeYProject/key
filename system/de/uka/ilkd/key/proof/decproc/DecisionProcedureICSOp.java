// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.proof.decproc;


public abstract class DecisionProcedureICSOp {
    
    // OPERATORS
    /** the ususal 'negation' operator '-' */
    public static final String NOT = "~";
    /** the ususal 'and' operator '/\' (be A, B formulae then 'A /\ B'
     * is true if and only if A is true and B is true */
    public static final String AND = "&";
    /** the ususal 'or' operator '\/' (be A, B formulae then 'A \/ B'
     * is true if and only if A is true or B is true */
    public static final String OR = "|";
    /** the ususal 'implication' operator '->' (be A, B formulae then
     * 'A -> B' is true if and only if A is false or B is true */
    public static final String IMP = "=>";
    /** the ususal 'equivalence' operator '<->' (be A, B formulae then       
     * 'A <->  B' is true if and only if A and B have the same truth
     * value */ 
    public static final String EQV = "<=>";

    /** the usual arithmetic operations: */
    public static final String PLUS = "+";
    public static final String MINUS = "-";    
    public static final String MULT = "*";
    
    /** the ususal 'equality' operator '=' */
    public static final String EQUALS = "=";
    /** the ususal 'less than' operator '<' */
    public static final String LT = "<";
    /** the ususal 'greater than' operator '>' */
    public static final String GT = ">";
    /** the ususal 'less than or equal' operator '<=' */
    public static final String LEQ = "<=";
    /** the ususal 'greater than or equal' operator '>=' */
    public static final String GEQ = ">=";

    /** the ususal 'forall' operator 'all' (be A a formula then       
     * 'all x.A' is true if and only if for all elements d of the
     * universe A{x<-d} (x substitued with d) is true */     
    public static final String ALL = null;
    /** the ususal 'exists' operator 'ex' (be A a formula then       
     * 'ex x.A' is true if and only if there is at least one elements
     * d of the universe such that A{x<-d} (x substitued with d) is true */     
    public static final String EX = null;
    /** the true constant */
    public static final String TRUE = "tt";
    /** the false constant */
    public static final String FALSE = "ff";

    /** some facts about byte_MAX and friends */
    public static final String LIMIT_FACTS = "";
    /*	+ "assert byte_RANGE = 256."
	+ "assert short_RANGE = 65536."
	+ "assert int_RANGE = 4294967296."
	+ "assert long_RANGE = 18446744073709551616."
	+ "assert byte_HALFRANGE = 128."
	+ "assert short_HALFRANGE = 32768."
	+ "assert int_HALFRANGE = 2147483648."
	+ "assert long_HALFRANGE = 9223372036854775808."
	+ "assert byte_MIN = -128."
	+ "assert short_MIN = -32768."
	+ "assert int_MIN = -2147483648."
	+ "assert long_MIN = -9223372036854775808."
	+ "assert byte_MAX = 127."
	+ "assert short_MAX = 32767."
	+ "assert int_MAX = 2147483647."
	+ "assert long_MAX = 9223372036854775807."
	+ "\n";
    */
}
