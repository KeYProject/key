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


public abstract class DecisionProcedureSimplifyOp {
    
    // OPERATORS
    /** the ususal 'negation' operator '-' */
    public static final String NOT = "NOT";
    /** the ususal 'and' operator '/\' (be A, B formulae then 'A /\ B'
     * is true if and only if A is true and B is true */
    public static final String AND = "AND";
    /** the ususal 'or' operator '\/' (be A, B formulae then 'A \/ B'
     * is true if and only if A is true or B is true */
    public static final String OR = "OR";
    /** the ususal 'implication' operator '->' (be A, B formulae then
     * 'A -> B' is true if and only if A is false or B is true */
    public static final String IMP = "IMPLIES";
    /** the ususal 'equivalence' operator '<->' (be A, B formulae then       
     * 'A <->  B' is true if and only if A and B have the same truth
     * value */ 
    public static final String EQV = "IFF";

    /** the usual arithmetic operations: */
    public static final String PLUS = "+";
    public static final String MINUS = "-";    
    public static final String MULT = "*";
    
    /** the ususal 'equality' operator '=' */
    public static final String EQUALS = "EQ";
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
    public static final String ALL = "FORALL";
    /** the ususal 'exists' operator 'ex' (be A a formula then       
     * 'ex x.A' is true if and only if there is at least one elements
     * d of the universe such that A{x<-d} (x substitued with d) is true */     
    public static final String EX = "EXISTS";
    /** the true constant */
    public static final String TRUE = "TRUE";
    /** the false constant */
    public static final String FALSE = "FALSE";

    /** some facts about byte_MAX and friends */
    public static final String LIMIT_FACTS =
	"(AND "
	+ "(< (long_MIN) (int_MIN))"
	+ "(< (int_MIN) (short_MIN))"
	+ "(< (short_MIN) (byte_MIN))"	
	+ "(< (byte_MIN) 0)"
	+ "(< 0 (byte_MAX))"
	+ "(< (byte_MAX) (short_MAX))"
	+ "(< (short_MAX) (int_MAX))"
	+ "(< (int_MAX) (long_MAX))"	
	+ "(EQ (byte_HALFRANGE) (+ (byte_MAX) 1))"	
	+ "(EQ (short_HALFRANGE) (+ (short_MAX) 1))"	
	+ "(EQ (int_HALFRANGE) (+ (int_MAX) 1))"	
	+ "(EQ (long_HALFRANGE) (+ (long_MAX) 1))"
	+ "(EQ (byte_MIN) (- 0 (byte_HALFRANGE)))"
	+ "(EQ (short_MIN) (- 0 (short_HALFRANGE)))"
	+ "(EQ (int_MIN) (- 0 (int_HALFRANGE)))"
	+ "(EQ (long_MIN) (- 0 (long_HALFRANGE)))"
	+ "(EQ (byte_RANGE) (* 2 (byte_HALFRANGE)))"
	+ "(EQ (short_RANGE) (* 2 (short_HALFRANGE)))"
	+ "(EQ (int_RANGE) (* 2 (int_HALFRANGE)))"
	+ "(EQ (long_RANGE) (* 2 (long_HALFRANGE)))"
	+ "(EQ (byte_MAX) 127)"
	+ "(EQ (short_MAX) 32767)"
	+ ")\n";
}
