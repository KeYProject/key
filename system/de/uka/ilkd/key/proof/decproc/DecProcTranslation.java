// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.decproc;
import java.util.*;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;
/**
 * Represents a try to remove code duplication.
 */
public abstract class DecProcTranslation {
	/**
	 * Just a constructor which starts the conversion to Simplify syntax. The
	 * result can be fetched with
	 * 
	 * @param sequent
	 *           The sequent which shall be translated.
	 * @param cs
	 *           The constraints which shall be incorporated.
	 * @param localmv
	 *           The local metavariables, should be the ones introduced after
	 *           the last branch.
	 */
	public DecProcTranslation(Sequent sequent, ConstraintSet cs,
			SetOfMetavariable localmv, Services services)
			throws SimplifyException {
		constraintSet = cs;
		localMetavariables = localmv;
		this.services = services;
	}
	/**
	 * Returns the sequent given with the constructor in Simplify 
	 * syntax (as far as possible)
	 * @returns The sequent given with the constructor in Simplify 
	 * syntax (as far as possible)
	 */
	public String getText() {
		return text;
	}
	
	/**
	 * Returns a unique HashCode for the object qv.
	 * Unique means unique for the goal given to the calling class.
	 * This function does not depend on .hashcode() to deliver unique 
	 * hash codes like the memory address of the object. It uses a 
	 * hashMap and compares every new Object in O(n) (n number of 
	 * Objects with the same .hashCode()) to all others.
         * @param qv the Object the hashcode should be returned.
	 * @returns a unique hashcode for the variable gv.
	 */
	public int getUniqueHashCode(Object qv) {
		Integer number = (Integer) this.variableMap.get(qv);
		if (number == null) {
			number = new Integer(this.variableMap.size());
			this.variableMap.put(qv, number);
		}
		return number.intValue();
	}
	/**
	 * Returns a unique HashCode for the term qv.
	 * Unique means unique for the goal given to the calling class.
	 * This function does not depend on .hashcode() to deliver 
	 * unique hash codes like the memory address of the object. 
	 * It uses a hashMap and compares
	 * every new Object in O(n) (n number of Objects 
	 * with the same .hashCode()) to all others.
	 * It compares with .equalsModRenaming().
	 * @returns a unique hashcode for the term gv.
	 * @param term the Term the hashcode should be returned.
	 */
	public int getUniqueHashCodeForUninterpretedTerm(Term term) {
		Integer number = (Integer) this.variableMap
				.get(new UninterpretedTermWrapper(term));
		if (number == null) {
			number = new Integer(this.variableMap.size());
			this.variableMap.put(new UninterpretedTermWrapper(term), number);
		}
		return number.intValue();
	}
	
	/**
	 * Replaces a modulo with a set of (in-)equalities. 'a mod b' becomes the c
	 * in 'a=k*b+c'. '(a = k*b+c) & (c &gt;= 0) & (c &lt; b)'. These constraints
	 * are added as global constraints. The same Term is never converted twice,
	 * the 'c' calculated before is taken. This way we ensure that constraints
	 * are added just once.
	 * As a guard '!(b=0)->' is added in front of these constraints.
	 * 
	 * @param t
	 *           The Term to be replaced
	 * @param quantifiedVars
	 *           a Vector containing all variables that have been bound in
	 *           super-terms. It is only used for the translation of modulo
	 *           terms, but must be looped through until we get there.
	 * @return The 'c' of '(a = k*b+c)'
	 */
// 	protected Term translateModulo(Term t, Vector quantifiedVars) {
// 		if (moduloReplacements.containsKey(t)) {
// 			return (Term) moduloReplacements.get(t);
// 		}
// 		TermFactory tf = new TermFactory();
// 		final AbstractIntegerLDT integerLDT = services.getTypeConverter()
// 				.getIntegerLDT();
// 		final Sort intSort = integerLDT.targetSort();
		
// 		if (quantifiedVars.size() > 0) {
// 			return null;
// 		}
		
// 		// let the modulo term be "a mod b"
// 		// and the replacement c for which the following constraints hold:
// 		// 	(!(b=0))->
// 		// variable k, 
// 		Term k = tf.createFunctionTerm(new LogicVariable(new Name("k"
// 				+ moduloCounter), intSort));
// 		// b = 0
// 		Term be0 = tf.createEqualityTerm(t.sub(1), integerLDT
// 				.translateLiteral(new IntLiteral(0)));
// 		// !(b=0)
// 		Term nbe0 = tf.createJunctorTerm(Op.NOT, be0);
// 		// variable c
// 		Term c = tf.createFunctionTerm(new LogicVariable(new Name("c"
// 				+ moduloCounter), intSort));
// 		// k * b
// 		Term mul = tf.createFunctionTerm(integerLDT.getFunctionFor(new Times(
// 				null, null)), k, t.sub(1));
// 		// (k*b)+c
// 		Term plus = tf.createFunctionTerm(integerLDT.getFunctionFor(new Plus(
// 				null, null)), mul, c);
// 		// a = (k*b)+c
// 		Term eq = tf.createEqualityTerm(t.sub(0), plus);
// 		// c >= 0
// 		Term ge = tf.createFunctionTerm(integerLDT
// 				.getFunctionFor(new GreaterOrEquals(new ExtList())), c,
// 				integerLDT.translateLiteral(new IntLiteral(0)));
// 		// TODO Java modulo semantic, c > -b
// 		// c < b
// 		Term lt = tf.createFunctionTerm(integerLDT.getFunctionFor(new LessThan(
// 				new ExtList())), c, t.sub(1));
// 		// !(b=0)-> a = (k*b)+c
// 		Term impeq = tf.createJunctorTerm(Op.IMP, nbe0, eq);
// 		// !(b=0)-> c >= 0
// 		Term impge = tf.createJunctorTerm(Op.IMP, nbe0, ge);
// 		// !(b=0)-> c < b
// 		Term implt = tf.createJunctorTerm(Op.IMP, nbe0, lt);
// 		moduloConstraints.add(impeq);
// 		moduloConstraints.add(impge);
// 		moduloConstraints.add(implt);
// 		usedLocalMv.add(c.op());
// 		usedLocalMv.add(k.op());
// 		if (nogger.isDebugEnabled()) {
// 			nogger.debug("c.op(): " + c.op().name());
// 		}
// 		moduloCounter++;
// 		moduloReplacements.put(t, c);
// 		return c;
// 	}
	
	/**
	 * Takes all the modulo constraints already collected and conjoins them 
	 * conjunctivly.
	 * @return the conjunctivly conjoined modulo constraints. 
	 */
// 	protected Term moduloConjoin() {
// 		if (nogger.isDebugEnabled()) {
// 			nogger.debug("Entered ModuloConjoin, number is " + moduloConstraints.size());
// 		}
// 		TermFactory tf = new TermFactory();
// 		Term[] mc = new Term[moduloConstraints.size()];
// 		for (int i = 0; i < moduloConstraints.size(); i++) {
// 			mc[i] = (Term)moduloConstraints.get(i);
// 		}
// 		if (mc.length == 0) {
// 			return tf.createJunctorTerm(Op.TRUE);
// 		} else if (mc.length == 1) {
// 			return mc[0];
// 		}
// 		Term h = mc[0];
// 		int i = 1;
// 		do {
// 			h = tf.createJunctorTerm(Op.AND, h, mc[i]);
// 		} while (i++ < mc.length - 1);
// 		return h;
// 	}

	/**
	 * 
	 * Eliminates the modulo from all the modulo constraints . First, does a
	 * bogus translate to collect all first class modulos. Then goes through all
	 * modulo constraints, tries to convert them into the decision procedures
	 * input language, and, most important, while this happens, new modulo
	 * constraints may be found. These are added to moduloConstraints. Since
	 * modulo terms are never replaced in the term structure, just in the output
	 * for the decision procedure, this just ensures, that afterwards we have a
	 * list that really contains all modulo constraints.
	 * 
	 * @throws SimplifyException 
	 */
// 	protected void computeModuloConstraints(Sequent seq) throws SimplifyException {
// 		translate(seq.antecedent(), ANTECEDENT); //I just want the side effects
// 		translate(seq.succedent(), SUCCEDENT); //I just want the side effects
// 		// here moduloConstraints is a moving target, 
// 		// as long as new constraints are added, the loop shall go on!
// 		for (int i = 0; i < moduloConstraints.size(); i ++) { 
// 			translate((Term)moduloConstraints.get(i), ANTECEDENT, new Vector());
// 		}
// 	}
	/**
	 * Just copies the quantified variables of term into quantifiedVars
	 * @param quantifiedVars
	 * @param term
	 */
	protected void collectQuantifiedVars (Vector quantifiedVars, Term term) {
		ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
		for (int i = 0; i < vars.size(); ++i) {
			quantifiedVars.add(vars.getQuantifiableVariable(i));
		}
	}
	
	/** The translation result is stored in this variable. */
	protected String text;
	/** StringBuffer contains all declared predicate symbols. */
	protected final StringBuffer predicate = new StringBuffer();
	/** StringBuffer to store text which could be usefull for the user */
	protected final StringBuffer notes = new StringBuffer();
	/** remember all printed predicates */
	protected final Set predicateSet = new HashSet();
	/** The Constraint under which the sequent is to be proven */
	protected final ConstraintSet constraintSet;
	/**
	 * Some terms should need a unique HashCode (CVC doesn't handle quantors,
	 * ProgramVariables from different blocks could have the same name),
	 * functions and user named skolemfunctions can get the same name. The
	 * difference to variables is that the have quantified variables so they
	 * have to be compared moduloRenaming. Comparing terms without variables
	 * with .equals() instead of .equalsModRenaming() should give a speed
	 * improvement.
	 */
	protected final HashMap variableMap = new HashMap();
	/**
	 * To handle local metavariabls we have to quantify them existentially. We
	 * do not need to quantify already substituted metavariables.
	 */
	protected final HashSet usedLocalMv = new HashSet();
	protected final HashSet usedGlobalMv = new HashSet();
	protected final SetOfMetavariable localMetavariables;
	protected final HashMap moduloReplacements = new HashMap();
	protected final List moduloConstraints = new ArrayList();
	protected int moduloCounter = 0;
	protected final Services services;
	protected static final int ANTECEDENT = 0;
	protected static final int SUCCEDENT = 1;
	protected static final int YESNOT = 2;

	static Logger nogger = Logger.getLogger(DecProcTranslation.class.getName());

	/**
	 * Translates the given term into the decision procedure's input syntax and
	 * and returns the resulting StringBuffer sb.
	 * 
	 * @param term
	 *           the Term which should be written in Simplify syntax
	 * @param skolemization
	 *           Indicates whether the formula is in the ANTECEDENT, SUCCEDENT
	 *           or with YESNOT if a "not" operation occurres above the term
	 *           which will prevent skolemization ("not"s are not counted). For
	 *           Simplify this parameter is ignored.
	 * @param quantifiedVars
	 *           a Vector containing all variables that have been bound in
	 *           super-terms. It is only used for the translation of modulo
	 *           terms, but must be looped through until we get there.
	 */
	protected abstract StringBuffer translate(Term term, int skolemization, Vector quantifiedVars) throws SimplifyException;

	/** Translates the given sequent into the decision procedure's input syntax 
    *
    * @param sequent the Sequent which should be translated
    * @return the translated version of s
    */
	protected abstract StringBuffer translate(Sequent sequent) throws SimplifyException;

	/**
	 * Translates the given Semisequent into the decision procedure's input
	 * syntax and returns the resulting StringBuffer sb.
	 * 
	 * @param ss
	 *           the SemiSequent which should be written in the decision
	 *           procedure's syntax
	 * @param skolemization
	 *           Indicates whether the formula is in the ANTECEDENT, SUCCEDENT
	 *           or with YESNOT if a "not" operation occurres above the term
	 *           which will prevent skolemization for ICS ("not"s are not
	 *           counted). For Simplify this parameter is ignored.
	 */	
	protected abstract StringBuffer translate(Semisequent ss, int skolemization) throws SimplifyException;

/*	protected abstract StringBuffer translate(Semisequent ss, 
						  int skolemization,
						  boolean lightWeight) 
						  throws SimplifyException;*/
}
