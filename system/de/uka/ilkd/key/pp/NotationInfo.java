// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;

import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.Service;


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
 * Support for infix notations in case of function symbols like 
 * <code>+, -, *, /, <, >, </code> 
 * etc. is added by class {@link de.uka.ilkd.key.pp.PresentationFeatures} (that has 
 * historical reasons)
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
public class NotationInfo {

    /** Factory method: creates a new NotationInfo instance. The
     * actual implementation depends on system properties or service
     * entries. */
    public static final NotationInfo createInstance() {
	return (NotationInfo) Service.find(NotationInfo.class.getName(),
					   NotationInfo.class.getName());
    }
    
    
    /** This maps operators and classes of operators to {@link
     * Notation}s.  The idea is that we first look wether the operator has
     * a Notation registered.  Otherwise, we see if there is one for the
     * <em>class</em> of the operator.
     */
    protected HashMap tbl;

    /**
     * Maps terms to abbreviations and reverse.
     */
    protected AbbrevMap scm;


    /** Create a new NotationInfo. Do not call this constructor
     * directly. Use the factory method {@link #createInstance()}
     * instead. */
    public NotationInfo() {
    	createDefaultNotationTable();
    }

    /** Set all notations back to default. */
    public void setBackToDefault() {
    	createDefaultNotationTable();
    }
    
    /** Register the standard set of notations.  This means no
     * abbreviations, and a set of Notations for the built-in operators
     * which corresponds to the parser syntax. 
     */
    protected void createDefaultNotationTable() {
		tbl=new HashMap();
		createDefaultOpNotation();
		createDefaultTermSymbolNotation();
		scm = new AbbrevMap();
    }

    /**
     * Registers notations for the built-in operators.  The priorities
     * and associativities correspond to the parser syntax.  
     */
   protected void createDefaultOpNotation() {
	tbl.put(Op.TRUE ,new Notation.Constant("true", 130));
	tbl.put(Op.FALSE,new Notation.Constant("false", 130));
	tbl.put(Op.NOT,new Notation.Prefix("!" ,60,60));
	tbl.put(Op.AND,new Notation.Infix("&"  ,50,50,60));
	tbl.put(Op.OR, new Notation.Infix("|"  ,40,40,50));
	tbl.put(Op.IMP,new Notation.Infix("->" ,30,40,30));
	tbl.put(Op.EQV,new Notation.Infix("<->",20,20,30));

    	tbl.put(Op.ALL,new Notation.Quantifier("\\forall", 60, 60));
	tbl.put(Op.EX, new Notation.Quantifier("\\exists", 60, 60));
	tbl.put(Op.SUM, new Notation.NumericalQuantifier("\\sum", 60, 60, 70));
	tbl.put(Op.BSUM, new Notation.BoundedNumericalQuantifier("\\bSum", 60, 60, 70));
	tbl.put(Op.PRODUCT, new Notation.NumericalQuantifier("\\product", 60, 60, 70));
	tbl.put(Op.DIA,new Notation.Modality("\\<","\\>", 60, 60));
	tbl.put(Op.BOX,new Notation.Modality("\\[","\\]", 60, 60));
	tbl.put(Op.TOUT,new Notation.Modality("\\[[","\\]]", 60, 60));
	Modality modalities[] = {Op.DIATRC, Op.BOXTRC, Op.TOUTTRC,
	                         Op.DIATRA, Op.BOXTRA, Op.TOUTTRA,
				 Op.DIASUSP, Op.BOXSUSP, Op.TOUTSUSP};
	for(int i=0; i<modalities.length;i++)
	  tbl.put(modalities[i],
	      new Notation.Modality("\\"+modalities[i].name().toString(),
	                            "\\endmodality",60, 60));
	tbl.put(Op.IF_THEN_ELSE, new Notation.IfThenElse(130, "\\if"));
	tbl.put(Op.IF_EX_THEN_ELSE, new Notation.IfThenElse(130, "\\ifEx"));

	//createNumLitNotation(IntegerLDT.getStaticNumberSymbol());

	tbl.put(Op.SUBST,new Notation.Subst());
    }    

    /** 
     * Register notations for standard classes of operators.  This
     * includes Function operators, all kinds of variables, etc.
     */
    /** 
     * Register notations for standard classes of operators.  This
     * includes Function operators, all kinds of variables, etc.
     */
   protected void createDefaultTermSymbolNotation() {
	tbl.put(Function.class, new Notation.Function());               
	tbl.put(LogicVariable.class, new Notation.VariableNotation());
	//tbl.put(SchemaVariable.class, new Notation.Variable());
	tbl.put(Metavariable.class, new Notation.MetavariableNotation());
	tbl.put(LocationVariable.class, new Notation.VariableNotation());
        tbl.put(ProgramConstant.class, new Notation.VariableNotation());
	tbl.put(ProgramMethod.class, new Notation.ProgramMethod(121));
	tbl.put(Equality.class, new Notation.Infix("=", 70, 80, 80)); 
	tbl.put(QuanUpdateOperator.class, new Notation.QuanUpdate());
	tbl.put(AnonymousUpdate.class, new Notation.AnonymousUpdate());
	tbl.put(ShadowAttributeOp.class, new Notation.ShadowAttribute(121,121));
	tbl.put(AttributeOp.class, new Notation.Attribute(121,121));
/*XXX
	tbl.put(ShadowArrayOp.class, new Notation.ArrayNot
		(new String[]{"[", "]", ""}, 130, new int[]{121, 0, 0}));
	tbl.put(ArrayOp.class, new Notation.ArrayNot(new String[]{ "[","]" } ,130, new int[]{121, 0}));
*/	
	tbl.put(CastFunctionSymbol.class, new Notation.CastFunction("(",")",120, 140));
	tbl.put(NRFunctionWithExplicitDependencies.class, 
		new Notation.NRFunctionWithDependenciesNotation());               
	tbl.put(ModalOperatorSV.class, new Notation.ModalSVNotation(60, 60));
	tbl.put(SortedSchemaVariable.class, new Notation.SortedSchemaVariableNotation());
    }

    public AbbrevMap getAbbrevMap(){
	return scm;
    }

    public void setAbbrevMap(AbbrevMap am){
	scm = am;
    }

    /** Get the Notation for a given Operator.  
     * If no notation is registered, a Function notation is returned.
     */
    public Notation getNotation(Operator op, Services services) {
	if(services != null) {
	    IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
	    if(integerLDT != null) {
		createNumLitNotation(integerLDT.getNumberSymbol());
		createCharLitNotation(integerLDT.getCharSymbol());
	    }
	}
	createStringLitNotation(de.uka.ilkd.key.java.TypeConverter.stringConverter.getStringSymbol(),null);

	//For OCL Simplification
	if (tbl.containsKey(op.name().toString())) {
	    return (Notation) tbl.get(op.name().toString());
	}
	//
	else if (tbl.containsKey(op)) {
	    return (Notation) tbl.get(op);
	} else if (tbl.containsKey(op.getClass())) {
	    return (Notation) tbl.get(op.getClass());
	} else if (op instanceof SortedSchemaVariable){
		return (Notation) tbl.get(SortedSchemaVariable.class);
	} else {
	    return new Notation.Function();
	}
    }

    /** Registers an infix notation for a given operator
     * @param op    the operator
     * @param token the string representing the operator
     */
    public void createInfixNotation(Operator op, String token) {
	tbl.put(op, new Notation.Infix(token,120,130,130));
    }

    /** Registers an infix notation for a given operator
     * with given priority and associativity
     * @param op    the operator
     * @param token the string representing the operator
     */
    public void createInfixNotation(Operator op, String token, int prio, int lass, int rass) {
	tbl.put(op, new Notation.Infix(token,prio,lass,rass));
    }

    /** Registers a prefix notation for a given operator 
     * @param op    the operator
     * @param token the string representing the operator
     */
    public void createPrefixNotation(Operator op, String token) {
	tbl.put(op, new Notation.Prefix(token, 140, 130));
    }

    /** Registers a number literal notation for a given operator.
     * This is done for the `Z' operator which marks number literals.
     * A term <code>Z(3(2(#)))</code> gets printed simply as
     * <code>23</code>.
     * @param op the operator */
    public void createNumLitNotation(Operator op) {
	tbl.put(op, new Notation.NumLiteral());
    }


    /** Registers a character literal notation for a given operator.
     * This is done for the `C' operator which marks character literals.
     * A term <code>C(3(2(#)))</code> gets printed simply as
     * the character corresponding to the unicode value 23 (really 23
     * and not 32, see integer literals)
     * @param op the operator */
    public void createCharLitNotation(Operator op) {
	tbl.put(op, new Notation.CharLiteral());
    }


    public void createStringLitNotation(Operator op, Operator eps) {
	Notation.StringLiteral stringLiteral =  new Notation.StringLiteral();
	tbl.put(op, stringLiteral);
	tbl.put(eps, stringLiteral);
    }
}
