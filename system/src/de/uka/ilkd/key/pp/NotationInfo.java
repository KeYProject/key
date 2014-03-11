// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.pp;

import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.WarySubstOp;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.UnicodeHelper;


/** 
 * <p> 
 * Stores the mapping from operators to {@link Notation}s.  Each 
 * {@link Notation} represents the concrete syntax for some 
 * {@link de.uka.ilkd.key.logic.op.Operator}.  The {@link LogicPrinter}
 * asks the NotationInfo to find out which Notation to use for a given term.
 * <p>
 * The Notation associated with an operator might change.  New Notations can
 * be added.
 * 
 * <p>
 * The next lines describe a general rule how to determine priorities and 
 * associativities:
 * 
 *  One thing we need to know from the pretty printer:
 *  Given a term <tt>t</tt> containg <tt>s</tt> as proper subterm. 
 *  Then <tt>s</tt> is printed in parentheses when the priority of the
 *  top level symbol of <tt>s</tt> is strict less than the associativity of the 
 *  position where <tt>s</tt> occurs. For example:
 *  <p>
 *   Let the priority of <tt>AND</tt> be <tt>30</tt> and the associativities for each 
 * of its subterms be 40; <tt>OR</tt>s priority is <tt>20</tt> and the associativites are 
 * both <tt>30</tt> then 
 *     <ul> <li> formula <tt>(p & q) | r</tt> is pretty printed as <tt>p & q | r</tt>
 *         as the priority of & is 30 which is (greater or) equal than the 
 *         associativity of <tt>OR</tt>s left subterm which is 30.</li>
 *         <li> In contrast the formula <tt>p & (q | r)</tt> is pretty printed as 
 *         <tt>p & (q | r)</tt> as the priority of <tt>OR</tt> is 20 which is less than 
 *         the associativity of <tt>AND</tt>s left subterm, which is 40.</li>
 *     </ul> 
 *         
 * A general rule to determine the correct priority and associativity is to use: 
 *  
 *  Grammar rules whose derivation delivers a syntactical correct logic term should follow 
 *  a standard numbering scheme, which is used as indicator for priorities and associativites, 
 *  e.g. 
 *   by simply reading the grammar rule 
 *          <blockquote><tt>term60 ::= term70 (IMP term70)?</tt></blockquote> 
 *   we get the priority of <tt>IMP</tt>, which is <tt>60</tt>. The associativities 
 *   of <tt>IMP</tt>s subterms are not much more difficult to determine, namely    
 *   the left subterm has associativity <tt>70</tt> and in this case its the same 
 *   for the right subterm (<tt>70</tt>).
 *  <p>
 *  There are exceptional cases for
 *  <ul>
 *  <li> <em>infix function</em> symbols that are left associative e.g. 
 *  <code>-, +</code>
 *     <blockquote> 
 *         <tt> term90 ::= term100 (PLUS term100)* </tt>
 *     </blockquote>           
 * then the associative for the right subterm is increased by <tt>1</tt>, 
 * i.e. here we have a priority of <tt>90</tt> for <tt>PLUS</tt> as infix operator, 
 * a left associativity of <tt>100</tt> <em>and</em> a right associativity of <tt>101</tt>
 * </li>
 * <li> update and substituition terms: for them their associativity is 
 * determined dynamically by the pretty printer depending if it is applied on a 
 * formula or term. In principal there should be two different
 * rules in the parser as then we could reuse the general rule from above, but 
 * there are technical reasons which causes this exception.
 * </li>
 * <li> some very few rules do not follow the usual parser design 
 * e.g. like
 *     <blockquote><tt>R_PRIO ::= SubRule_ASS1 | SubRule_ASS2 </tt></blockquote>
 *   where
 *      <blockquote><tt>SubRule_ASS2 ::= OP SubRule_ASS1</tt></blockquote> 
 * Most of these few rules could in general be rewritten to fit the usual scheme
 * e.g. as
 * <blockquote><tt> R_PRIO ::= (OP)? SubRule_ASS1</tt></blockquote> 
 * using the priorities and associativities of the so rewritten rules 
 * (instead of rewriting them actually) is a way to cope with them.   
 * </li>
 * </ul>
 */
public final class NotationInfo {
    


    // Priorities of operators (roughly corresponding to the grammatical structure in the parser.
    static final int PRIORITY_TOP = 0;
    static final int PRIORITY_EQUIVALENCE = 20;
    static final int PRIORITY_IMP = 30;
    static final int PRIORITY_OR = 40;
    static final int PRIORITY_AND = 50;
    static final int PRIORITY_NEGATION = 60;
    static final int PRIORITY_QUANTIFIER = 60;
    static final int PRIORITY_MODALITY = 60;
    static final int PRIORITY_POST_MODALITY = 60;
    static final int PRIORITY_EQUAL = 70;
    static final int PRIORITY_COMPARISON = 80;
    static final int PRIORITY_ARITH_WEAK = 90;
    static final int PRIORITY_BELOW_ARITH_WEAK = 91;
    static final int PRIORITY_ARITH_STRONG = 100;
    static final int PRIORITY_BELOW_ARITH_STRONG = 101;
    static final int PRIORITY_CAST = 120;
    static final int PRIORITY_ATOM = 130;
    static final int PRIORITY_BOTTOM = 140;
    static final int PRIORITY_LABEL = 140; // TODO: find appropriate value


    public static boolean PRETTY_SYNTAX = true;
    /**
     * Whether the very fancy notation is enabled
     * in which Unicode characters for logical operators
     * are printed.
     */
    public static boolean UNICODE_ENABLED = false;
    
    public static boolean HIDE_PACKAGE_PREFIX = false;
    
    /** This maps operators and classes of operators to {@link
     * Notation}s.  The idea is that we first look whether the operator has
     * a Notation registered.  Otherwise, we see if there is one for the
     * <em>class</em> of the operator.
     */
    private HashMap<Object, Notation> notationTable;

    /**
     * Caches for the different kinds of notations.
     * If a cache is yet unused, a shallow clone
     * of the current notation table is produced and assigned to it.
     */
    private HashMap<Object, Notation> defaultNotationCache = null;
    private HashMap<Object, Notation> fancyNotationCache = null;
    private HashMap<Object, Notation> veryFancyNotationCache = null;
    
    /**
     * Maps terms to abbreviations and reverse.
     */
    private AbbrevMap scm = new AbbrevMap();
    
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    

    public NotationInfo() {
    	createDefaultNotationTable();
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------     
    
        
    /** Register the standard set of notations (that can be defined without
     * a services object).
     */
    private void createDefaultNotationTable() {
        if (defaultNotationCache != null){
            notationTable = defaultNotationCache;
            return;
        }
    defaultNotationCache = new LinkedHashMap<Object,Notation>();
    HashMap<Object,Notation> tbl = defaultNotationCache;
	
	tbl.put(Junctor.TRUE ,new Notation.Constant("true", PRIORITY_ATOM));
	tbl.put(Junctor.FALSE,new Notation.Constant("false", PRIORITY_ATOM));
	tbl.put(Junctor.NOT,new Notation.Prefix("!" ,PRIORITY_NEGATION,PRIORITY_NEGATION));
	tbl.put(Junctor.AND,new Notation.Infix("&"  ,PRIORITY_AND,PRIORITY_AND,PRIORITY_MODALITY));
	tbl.put(Junctor.OR, new Notation.Infix("|"  ,PRIORITY_OR,PRIORITY_OR,PRIORITY_AND));
	tbl.put(Junctor.IMP,new Notation.Infix("->" ,PRIORITY_IMP,PRIORITY_OR,PRIORITY_IMP));
	tbl.put(Equality.EQV,new Notation.Infix("<->",PRIORITY_EQUIVALENCE,PRIORITY_EQUIVALENCE,PRIORITY_IMP));
	tbl.put(Quantifier.ALL,new Notation.Quantifier("\\forall", PRIORITY_QUANTIFIER, PRIORITY_QUANTIFIER));
	tbl.put(Quantifier.EX, new Notation.Quantifier("\\exists", PRIORITY_QUANTIFIER, PRIORITY_QUANTIFIER));
	tbl.put(Modality.DIA,new Notation.ModalityNotation("\\<","\\>", PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
	tbl.put(Modality.BOX,new Notation.ModalityNotation("\\[","\\]", PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
	tbl.put(Modality.TOUT,new Notation.ModalityNotation("\\[[","\\]]", PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
	tbl.put(Modality.DIA_TRANSACTION,new Notation.ModalityNotation("\\diamond_transaction","\\endmodality", PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
	tbl.put(Modality.BOX_TRANSACTION,new Notation.ModalityNotation("\\box_transaction","\\endmodality", PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
	tbl.put(Modality.TOUT_TRANSACTION,new Notation.ModalityNotation("\\throughout_transaction","\\endmodality", PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
	tbl.put(IfThenElse.IF_THEN_ELSE, new Notation.IfThenElse(PRIORITY_ATOM, "\\if"));
	tbl.put(IfExThenElse.IF_EX_THEN_ELSE, new Notation.IfThenElse(PRIORITY_ATOM, "\\ifEx"));
	tbl.put(WarySubstOp.SUBST,new Notation.Subst());
	tbl.put(UpdateApplication.UPDATE_APPLICATION, new Notation.UpdateApplicationNotation());
	tbl.put(UpdateJunctor.PARALLEL_UPDATE, new Notation.ParallelUpdateNotation());	
	
	tbl.put(Function.class, new Notation.FunctionNotation());               
	tbl.put(LogicVariable.class, new Notation.VariableNotation());
	tbl.put(LocationVariable.class, new Notation.VariableNotation());
        tbl.put(ProgramConstant.class, new Notation.VariableNotation());
	tbl.put(Equality.class, new Notation.Infix("=", PRIORITY_EQUAL, PRIORITY_COMPARISON, PRIORITY_COMPARISON)); 
	tbl.put(ElementaryUpdate.class, new Notation.ElementaryUpdateNotation());
	tbl.put(ModalOperatorSV.class, new Notation.ModalSVNotation(PRIORITY_MODALITY, PRIORITY_MODALITY));
	tbl.put(SchemaVariable.class, new Notation.SchemaVariableNotation());
	
	tbl.put(Sort.CAST_NAME, new Notation.CastFunction("(",")",PRIORITY_CAST, PRIORITY_BOTTOM));
	tbl.put(TermLabel.class, new Notation.LabelNotation("<<", ">>", PRIORITY_LABEL));
	this.notationTable = tbl;
    }
        
    
    /**
     * Adds notations that can only be defined when a services object is 
     * available.
     */
    @SuppressWarnings("unchecked")
    private void addFancyNotations(Services services) {
        if (fancyNotationCache != null){
            notationTable = fancyNotationCache;
            return;
        }
        fancyNotationCache = (HashMap<Object,Notation>) defaultNotationCache.clone();
    HashMap<Object,Notation> tbl = fancyNotationCache; 
     
	//arithmetic operators
	final IntegerLDT integerLDT 
		= services.getTypeConverter().getIntegerLDT();	
	tbl.put(integerLDT.getNumberSymbol(), new Notation.NumLiteral());
	tbl.put(integerLDT.getCharSymbol(), new Notation.CharLiteral());
	tbl.put(integerLDT.getLessThan(), new Notation.Infix("<", PRIORITY_COMPARISON, PRIORITY_ARITH_WEAK, PRIORITY_ARITH_WEAK));
	tbl.put(integerLDT.getGreaterThan(), new Notation.Infix("> ", PRIORITY_COMPARISON, PRIORITY_ARITH_WEAK, PRIORITY_ARITH_WEAK));
	tbl.put(integerLDT.getLessOrEquals(), new Notation.Infix("<=", PRIORITY_COMPARISON, PRIORITY_ARITH_WEAK, PRIORITY_ARITH_WEAK));
	tbl.put(integerLDT.getGreaterOrEquals(), new Notation.Infix(">=", PRIORITY_COMPARISON, PRIORITY_ARITH_WEAK, PRIORITY_ARITH_WEAK));
	tbl.put(integerLDT.getSub(), new Notation.Infix("-", PRIORITY_ARITH_WEAK, PRIORITY_ARITH_WEAK, PRIORITY_BELOW_ARITH_WEAK));
	tbl.put(integerLDT.getAdd(), new Notation.Infix("+", PRIORITY_ARITH_WEAK, PRIORITY_ARITH_WEAK, PRIORITY_BELOW_ARITH_WEAK));
	tbl.put(integerLDT.getMul(), new Notation.Infix("*", PRIORITY_ARITH_STRONG, PRIORITY_ARITH_STRONG, PRIORITY_BELOW_ARITH_STRONG));
	tbl.put(integerLDT.getDiv(), new Notation.Infix("/", PRIORITY_ARITH_STRONG, PRIORITY_ARITH_STRONG, PRIORITY_BELOW_ARITH_STRONG));
	tbl.put(integerLDT.getMod(), new Notation.Infix("%", PRIORITY_ARITH_STRONG, PRIORITY_ARITH_STRONG, PRIORITY_BELOW_ARITH_STRONG));
	tbl.put(integerLDT.getNeg(),new Notation.Prefix("-", PRIORITY_BOTTOM, PRIORITY_ATOM));
	tbl.put(integerLDT.getNegativeNumberSign(), new Notation.Prefix("-", PRIORITY_BOTTOM, PRIORITY_ATOM));
        	
	//heap operators
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	tbl.put(HeapLDT.SELECT_NAME, new Notation.SelectNotation());
	tbl.put(heapLDT.getStore(), new Notation.StoreNotation());
	tbl.put(heapLDT.getAnon(), new Notation.AnonNotation());
	tbl.put(heapLDT.getCreate(), new Notation.CreateNotation());
	tbl.put(heapLDT.getMemset(), new Notation.MemsetNotation());
	tbl.put(IObserverFunction.class, new Notation.ObserverNotation());
	tbl.put(IProgramMethod.class, new Notation.ObserverNotation());
	tbl.put(heapLDT.getLength(), new Notation.Postfix(".length"));

        // sequence operators
        final SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();
	tbl.put(seqLDT.getSeqLen(), new Notation.Postfix(".length"));
	
	//set operators
	final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
	tbl.put(setLDT.getSingleton(), new Notation.SingletonNotation());
	tbl.put(setLDT.getUnion(), new Notation.Infix("\\cup", PRIORITY_ATOM, PRIORITY_TOP, PRIORITY_TOP));
	tbl.put(setLDT.getIntersect(), new Notation.Infix("\\cap", PRIORITY_ATOM, PRIORITY_TOP, PRIORITY_TOP));
	tbl.put(setLDT.getSetMinus(), new Notation.Infix("\\setMinus", PRIORITY_ATOM, PRIORITY_TOP, PRIORITY_TOP));
	tbl.put(setLDT.getElementOf(), new Notation.ElementOfNotation());
        tbl.put(setLDT.getSubset(), new Notation.Infix("\\subset", PRIORITY_ATOM, PRIORITY_TOP, PRIORITY_TOP));
        tbl.put(setLDT.getAllFields(), new Notation.Postfix(".*"));
	
	//string operators
	final CharListLDT charListLDT 
		= services.getTypeConverter().getCharListLDT();
	tbl.put(charListLDT.getClConcat(), new Notation.Infix("+",PRIORITY_CAST,PRIORITY_ATOM,PRIORITY_ATOM));
	tbl.put(charListLDT.getClCons(), new CharListNotation());
	tbl.put(charListLDT.getClEmpty(), new Notation.Constant("\"\"",PRIORITY_BOTTOM));
	
	    this.notationTable = tbl;
    }
    
    /**
     * Add notations with Unicode symbols.
     * @param services
     */
    @SuppressWarnings("unchecked")
    private void addVeryFancyNotations(Services services){
        if (veryFancyNotationCache != null){
            notationTable = veryFancyNotationCache;
            return;
        }
        veryFancyNotationCache = (HashMap<Object, Notation>) fancyNotationCache.clone();
        HashMap<Object,Notation> tbl = veryFancyNotationCache;
        
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();  
        final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
//        tbl.put(Junctor.TRUE ,new Notation.Constant(""+UnicodeHelper.TOP, PRIORITY_ATOM));
//        tbl.put(Junctor.FALSE,new Notation.Constant(""+UnicodeHelper.BOT, PRIORITY_ATOM));
        tbl.put(Junctor.NOT,new Notation.Prefix(""+UnicodeHelper.NEG ,PRIORITY_NEGATION,PRIORITY_NEGATION));
        tbl.put(Junctor.AND,new Notation.Infix(""+UnicodeHelper.AND  ,PRIORITY_AND,PRIORITY_AND,PRIORITY_MODALITY));
        tbl.put(Junctor.OR, new Notation.Infix(""+UnicodeHelper.OR  ,PRIORITY_OR,PRIORITY_OR,PRIORITY_AND));
        tbl.put(Junctor.IMP,new Notation.Infix(""+UnicodeHelper.IMP ,PRIORITY_IMP,PRIORITY_OR,PRIORITY_IMP));
        tbl.put(Equality.EQV,new Notation.Infix(""+UnicodeHelper.EQV,PRIORITY_EQUIVALENCE,PRIORITY_EQUIVALENCE,PRIORITY_IMP));
        tbl.put(Quantifier.ALL,new Notation.Quantifier(""+UnicodeHelper.FORALL, PRIORITY_QUANTIFIER, PRIORITY_QUANTIFIER));
        tbl.put(Quantifier.EX, new Notation.Quantifier(""+UnicodeHelper.EXISTS, PRIORITY_QUANTIFIER, PRIORITY_QUANTIFIER));
        tbl.put(integerLDT.getLessOrEquals(), new Notation.Infix(""+UnicodeHelper.LEQ, PRIORITY_COMPARISON, PRIORITY_ARITH_WEAK, PRIORITY_ARITH_WEAK));
        tbl.put(integerLDT.getGreaterOrEquals(), new Notation.Infix(""+UnicodeHelper.GEQ, PRIORITY_COMPARISON, PRIORITY_ARITH_WEAK, PRIORITY_ARITH_WEAK));
        tbl.put(setLDT.getEmpty(), new Notation.Constant(""+UnicodeHelper.EMPTY, PRIORITY_ATOM));
        tbl.put(setLDT.getUnion(), new Notation.Infix(""+UnicodeHelper.UNION, PRIORITY_ATOM, PRIORITY_TOP, PRIORITY_TOP));
        tbl.put(setLDT.getIntersect(), new Notation.Infix(""+UnicodeHelper.INTERSECT, PRIORITY_ATOM, PRIORITY_TOP, PRIORITY_TOP));
        tbl.put(setLDT.getSetMinus(), new Notation.Infix(""+UnicodeHelper.SETMINUS, PRIORITY_ATOM, PRIORITY_TOP, PRIORITY_TOP));
        tbl.put(setLDT.getElementOf(), new Notation.ElementOfNotation(" " + UnicodeHelper.IN + " "));
        tbl.put(setLDT.getSubset(), new Notation.Infix(""+UnicodeHelper.SUBSET, PRIORITY_ATOM, PRIORITY_TOP, PRIORITY_TOP));
        tbl.put(services.getTypeConverter().getHeapLDT().getPrec(), new Notation.Infix(""+UnicodeHelper.PRECEDES, PRIORITY_ATOM,PRIORITY_TOP, PRIORITY_TOP));
        tbl.put(TermLabel.class, new Notation.LabelNotation(""+UnicodeHelper.FLQQ, ""+UnicodeHelper.FRQQ, PRIORITY_LABEL));
        this.notationTable = tbl;
    }


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public void refresh(Services services) {
	createDefaultNotationTable();
	assert defaultNotationCache != null;
	if(PRETTY_SYNTAX && services != null) {
	    addFancyNotations(services);
	    if (UNICODE_ENABLED)
	        addVeryFancyNotations(services);
	}
    }    
        
    
    public AbbrevMap getAbbrevMap(){
	return scm;
    }
    

    public void setAbbrevMap(AbbrevMap am){
	scm = am;
    }

    Notation getNotation(Class<?> c) {
        return notationTable.get(c);
    }
    
    /** Get the Notation for a given Operator.  
     * If no notation is registered, a Function notation is returned.
     */
    Notation getNotation(Operator op) {
        Notation result = notationTable.get(op);
        if(result != null) {
            return result;
        }

        result = notationTable.get(op.getClass());
        if(result != null) {
            return result;
        }

        if(op instanceof SchemaVariable) {
            result = notationTable.get(SchemaVariable.class);
            if(result != null) {
                return result;
            }
        }
        
        if(op instanceof IProgramMethod) {
           result = notationTable.get(IProgramMethod.class);
           if(result != null) {
               return result;
           }
        }

        if(op instanceof IObserverFunction) {
           result = notationTable.get(IObserverFunction.class);
           if(result != null) {
               return result;
           }
        }

        if(op instanceof SortDependingFunction) {
            result = notationTable.get(((SortDependingFunction)op).getKind());
            if(result != null) {
                return result;
            }
        }

        return new Notation.FunctionNotation();
    }
}
