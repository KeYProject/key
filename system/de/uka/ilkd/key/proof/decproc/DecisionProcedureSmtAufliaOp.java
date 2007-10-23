//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.proof.decproc;


/**
 * This abstract class provides the operators defined in the SMT-Lib for 
 * the sublogics AUFLIA and QF_AUFLIA
 * 
 * @author akuwertz
 * @version 1.3,  09/29/2006  (Added quantifier support; 
 *                             all operators for logic AUFLIA are now implemented)
 * 
 * @see <a href="http://goedel.cs.uiowa.edu/smtlib/logics/AUFLIA.smt">AUFLIA</a>
 * @see <a href="http://goedel.cs.uiowa.edu/smtlib/logics/QF_AUFLIA.smt">QF_AUFLIA</a>
 */
public abstract class DecisionProcedureSmtAufliaOp {
    
    /*  OPERATORS in the AUFLIA-logic */        
        
    // Logical connectives in formulae        
    /** the usual 'negation' operator '-' (interpreted connective) */
    public static final String NOT = "not";    
    /** the usual 'and' operator '/\' (be A, B formulae then 'A /\ B'
     * is true if and only if A is true and B is true (interpreted connective) */
    public static final String AND = "and";    
    /** the usual 'or' operator '\/' (be A, B formulae then 'A \/ B'
     * is true if and only if A is true or B is true (interpreted connective) */
    public static final String OR = "or";
    /** the usual 'equivalence' operator '<->' (be A, B formulae then       
     * 'A <->  B' is true if and only if A and B have the same truth
     * value (interpreted connective) */ 
    public static final String EQV = "iff";
    /** the usual 'xor' or 'antivalence' operator 'xor' (be A, B formulae
     *  then 'A xor B' is true if and only if A and B have different truth
     *  values (interpreted connective) */
    public static final String XOR = "xor";
    /** the usual 'implication' operator '->' (be A, B formulae then
     * 'A -> B' is true if and only if A is false or B is true (interpreted connective) */
    public static final String IMP = "implies";

    
    
    // Interpreted predicate symbols
    /** the usual 'equality' operator '=' (interpreted predicate) */
    public static final String EQUALS = "=";
    /** the usual 'less than or equal' operator '<=' (interpreted predicate) */
    public static final String LEQ = "<=";
    /** the usual 'less than' operator '<' (interpreted predicate) */
    public static final String LT = "<";
    /** the usual 'greater than or equal' operator '>=' (interpreted predicate) */
    public static final String GEQ = ">=";
    /** the usual 'greater than' operator '>' (interpreted predicate) */
    public static final String GT = ">";
    /** the true constant */
    public static final String TRUE = "true";
    /** the false constant */
    public static final String FALSE = "false";
    /** a pairwise different predicate for convenience (interpreted) */
    public static final String DISTINCT = "distinct";
    
    
    
    // Quantifier symbols
    /** the usual 'all' quantifier */
    public static final String FORALL = "forall";
    /** the usual 'exists' quantifier */
    public static final String EXISTS = "exists";
    
    
        
    // Interpreted function symbols
    /** the usual arithmetic 'plus' operater (interpreted function) */
    public static final String PLUS = "+";
    /** the usual arithmetic 'minus' operater (interpreted function) */
    public static final String MINUS = "-";    
    /** the usual arithmetic 'multiply' operater (interpreted function) */
    public static final String MULT = "*";
    /** the unary minus, denoting the additive inverse of a number (interpreted function) */
    public static final String UMINUS = "~";
    
    /** Array access operation for selecting an array element (interpreted function) */
    public static final String SELECT = "select";
    /** Array access operation for storing an element (interpreted function) */
    public static final String STORE = "store";
    
    
    
    // Constructs for convenience
     /** the let construct for terms (Be t a term, f a formula and x a (term) variable
     * then 'let x=t in f' is semantically equivalent to the formula obtained from f
     *  by simultaneously replacing every occurrence of x in f by t */
    public static final String LET = "let";
    
    /** the flet construct for formulae (Be f1, f0 formulae and e a (formula) variable
     * then 'flet e=f0 in f1' is semantically equivalent to the formula obtained from f1 by 
     * simultaneously replacing every occurrence of e in f1 by f0 */ 
    public static final String FLET = "flet";
  
    /** the if-then-else construct for terms, which is very similiar to the 
     * '?' operator in java (Be f a formula, t1 and t2 terms then 'ite (f, t1, t2)'
     * evaluates to the value of t1 in every interpretation that makes f true, 
     * and to the value of t2 in every interpretation that makes f false */
    public static final String ITE = "ite";
    
    /** the if-then-else construct for formulae, can be seen as Shannon Operator for 
     * formulae (be A, B and C formulae then 'if A then B else C' is true if and only
     * if either A is true and B is true or A is false and C is true */
    public static final String IFTHENELSE = "if_then_else";
    
    
   
    // Interpreted sort symbols
    /** the usual set of integer numbers (interpreted sort) */
    public static final String INT = "Int";
    /** the usual functional array (interpreted sort) */
    public static final String ARRAY = "Array";
    
    
    
    /** An array of <tt>String</tt>s containing all interpreted symbols in AUFLIA.
     * <p> 
    /* It is used to ensure that the operator name of newly created uninterpreted symbols doesn't
     * match an interpreted symbol. Therefore this array has to be updated on adding or removing 
     * operators */ 
    private static final String[] 
        allSmtOperators = { NOT , AND , OR , EQV , XOR , IMP , EQUALS , GT , GEQ , LT , LEQ , 
                            TRUE , FALSE , DISTINCT , PLUS , MINUS, MULT , UMINUS , SELECT , 
                            STORE , LET , FLET , ITE , IFTHENELSE , INT , ARRAY  
                           };
    
    /** Returns an array containing all interpreted symbols in AUFLIA, which could be used to
     * check if a function, predicate or variable name or any arbitrary identifier equals one of
     * those interpreted symbols.
     * 
     * @return an array of <tt>String</tt>s containing all interpreted symbols in AUFLIA
     */
    public static final String[] getAllSmtOperators() { 
        return ( String[] ) allSmtOperators.clone(); 
    }
    
            
    
    //*ToDo* Is this needed for SMT AUFLIA?
// Will be added if needed
//    /** some facts about byte_MAX and friends */
//    public static final String LIMIT_FACTS =
//    "(and "
//    + "(< (long_MIN) (int_MIN))"
//    + "(< (int_MIN) (short_MIN))"
//    + "(< (short_MIN) (byte_MIN))"  
//    + "(< (byte_MIN) 0)"
//    + "(< 0 (byte_MAX))"
//    + "(< (byte_MAX) (short_MAX))"
//    + "(< (short_MAX) (int_MAX))"
//    + "(< (int_MAX) (long_MAX))"    
//    + "(EQ (byte_HALFRANGE) (+ (byte_MAX) 1))"  
//    + "(EQ (short_HALFRANGE) (+ (short_MAX) 1))"    
//    + "(EQ (int_HALFRANGE) (+ (int_MAX) 1))"    
//    + "(EQ (long_HALFRANGE) (+ (long_MAX) 1))"
//    + "(EQ (byte_MIN) (- 0 (byte_HALFRANGE)))"
//    + "(EQ (short_MIN) (- 0 (short_HALFRANGE)))"
//    + "(EQ (int_MIN) (- 0 (int_HALFRANGE)))"
//    + "(EQ (long_MIN) (- 0 (long_HALFRANGE)))"
//    + "(EQ (byte_RANGE) (* 2 (byte_HALFRANGE)))"
//    + "(EQ (short_RANGE) (* 2 (short_HALFRANGE)))"
//    + "(EQ (int_RANGE) (* 2 (int_HALFRANGE)))"
//    + "(EQ (long_RANGE) (* 2 (long_HALFRANGE)))"
//    + "(EQ (byte_MAX) 127)"
//    + "(EQ (short_MAX) 32767)"
//    + ")\n";
}
