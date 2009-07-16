// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.unittest.simplify.translation;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.IteratorOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.util.Debug;

/**
 * 
 * @author daniels
 * 
 *         The class responsible for converting a sequent into the Simplify
 *         input language. It is public because ASM-KeY inherits form it to
 *         provide a version suppporting asm operators.
 */
public class SimplifyTranslation {

    /** the ususal 'negation' operator '-' */
    private static final String NOT = "NOT";

    /**
     * the ususal 'and' operator '/\' (be A, B formulae then 'A /\ B' is true if
     * and only if A is true and B is true
     */
    private static final String AND = "AND";

    /**
     * the ususal 'or' operator '\/' (be A, B formulae then 'A \/ B' is true if
     * and only if A is true or B is true
     */
    private static final String OR = "OR";

    /**
     * the ususal 'implication' operator '->' (be A, B formulae then 'A -> B' is
     * true if and only if A is false or B is true
     */
    private static final String IMP = "IMPLIES";

    /**
     * the ususal 'equivalence' operator '<->' (be A, B formulae then 'A <-> B'
     * is true if and only if A and B have the same truth value
     */
    private static final String EQV = "IFF";

    /** the usual arithmetic operations: */
    private static final String PLUS = "+";

    private static final String MINUS = "-";

    private static final String MULT = "*";

    /** the ususal 'equality' operator '=' */
    private static final String EQUALS = "EQ";

/** the ususal 'less than' operator '<' */
    private static final String LT = "<";

    /** the ususal 'greater than' operator '>' */
    private static final String GT = ">";

    /** the ususal 'less than or equal' operator '<=' */
    private static final String LEQ = "<=";

    /** the ususal 'greater than or equal' operator '>=' */
    private static final String GEQ = ">=";

    /**
     * the ususal 'forall' operator 'all' (be A a formula then 'all x.A' is true
     * if and only if for all elements d of the universe A{x<-d} (x substitued
     * with d) is true
     */
    private static final String ALL = "FORALL";

    /**
     * the ususal 'exists' operator 'ex' (be A a formula then 'ex x.A' is true
     * if and only if there is at least one elements d of the universe such that
     * A{x<-d} (x substitued with d) is true
     */
    private static final String EX = "EXISTS";

    /** the true constant */
    private static final String TRUE = "TRUE";

    /** the false constant */
    private static final String FALSE = "FALSE";

    /** The translation result is stored in this variable. */
    private String text;

    /** StringBuffer contains all declared predicate symbols. */
    private final StringBuffer predicate = new StringBuffer();

    /** StringBuffer to store text which could be usefull for the user */
    private final StringBuffer notes = new StringBuffer();

    /** remember all printed predicates */
    private final Set<String> predicateSet = new HashSet<String>();

    /** The Constraint under which the sequent is to be proven */
    private final ConstraintSet constraintSet;

    /**
     * Some terms should need a unique HashCode (CVC doesn't handle quantors,
     * ProgramVariables from different blocks could have the same name),
     * functions and user named skolemfunctions can get the same name. The
     * difference to variables is that the have quantified variables so they
     * have to be compared moduloRenaming. Comparing terms without variables
     * with .equals() instead of .equalsModRenaming() should give a speed
     * improvement.
     */
    private final HashMap<Object, Integer> variableMap = new HashMap<Object, Integer>();

    /**
     * To handle local metavariabls we have to quantify them existentially. We
     * do not need to quantify already substituted metavariables.
     */
    private final HashSet<Metavariable> usedLocalMv = new HashSet<Metavariable>();

    private final HashSet<Metavariable> usedGlobalMv = new HashSet<Metavariable>();

    private final SetOfMetavariable localMetavariables;

    private static final int ANTECEDENT = 0;

    private static final int SUCCEDENT = 1;

    static Logger nogger = Logger
	    .getLogger(SimplifyTranslation.class.getName());

    private HashMap<Term, StringBuffer> cacheForUninterpretedSymbols;

    private ListOfString sortAxioms = SLListOfString.EMPTY_LIST;

    private boolean quantifiersOccur = false;

    private Sort jbyteSort;

    private Sort jshortSort;

    private Sort jintSort;

    private Sort jlongSort;

    private Sort jcharSort;

    private Sort integerSort;

    private AbstractIntegerLDT integerLDT;

    private static long counter = 0;

    static Logger logger = Logger
	    .getLogger(SimplifyTranslation.class.getName());

    final TermFactory tf = TermFactory.DEFAULT;

    /**
     * Just a constructor which starts the conversion to Simplify syntax. The
     * result can be fetched with
     * 
     * @param sequent
     *            The sequent which shall be translated.
     * @param cs
     *            The constraints which shall be incorporated.
     * @param localmv
     *            The local metavariables, should be the ones introduced after
     *            the last branch.
     */
    public SimplifyTranslation(Sequent sequent, ConstraintSet cs,
	    SetOfMetavariable localmv, Services services, boolean lightWeight)
	    throws SimplifyException {
	// super(sequent, cs, localmv, services);
	constraintSet = cs;
	localMetavariables = localmv;
	integerLDT = services.getTypeConverter().getIntegerLDT();
	integerSort = integerLDT.targetSort();
	jbyteSort = services.getTypeConverter().getByteLDT().targetSort();
	jshortSort = services.getTypeConverter().getShortLDT().targetSort();
	jintSort = services.getTypeConverter().getIntLDT().targetSort();
	jlongSort = services.getTypeConverter().getLongLDT().targetSort();
	jcharSort = services.getTypeConverter().getCharLDT().targetSort();
	cacheForUninterpretedSymbols = new HashMap<Term, StringBuffer>();
	StringBuffer hb = translate(sequent, lightWeight);
	text = predicate.toString() + produceClosure(hb);
	logger.info("SimplifyTranslation:\n" + text);
	if (notes.length() > 0) {
	    logger.info(notes);
	}
    }

    /*
     * Returns the sequent given with the constructor in Simplify syntax (as far
     * as possible)
     * 
     * @returns The sequent given with the constructor in Simplify syntax (as
     * far as possible)
     */
    public String getText() {
	return text;
    }

    /**
     * Returns a unique HashCode for the object qv. Unique means unique for the
     * goal given to the calling class. This function does not depend on
     * .hashcode() to deliver unique hash codes like the memory address of the
     * object. It uses a hashMap and compares every new Object in O(n) (n number
     * of Objects with the same .hashCode()) to all others.
     * 
     * @param qv
     *            the Object the hashcode should be returned.
     * @returns a unique hashcode for the variable gv.
     */
    public int getUniqueHashCode(Object qv) {
	Integer number = this.variableMap.get(qv);
	if (number == null) {
	    number = new Integer(this.variableMap.size());
	    this.variableMap.put(qv, number);
	}
	return number.intValue();
    }

    /**
     * Returns a unique HashCode for the term qv. Unique means unique for the
     * goal given to the calling class. This function does not depend on
     * .hashcode() to deliver unique hash codes like the memory address of the
     * object. It uses a hashMap and compares every new Object in O(n) (n number
     * of Objects with the same .hashCode()) to all others. It compares with
     * .equalsModRenaming().
     * 
     * @returns a unique hashcode for the term gv.
     * @param term
     *            the Term the hashcode should be returned.
     */
    public int getUniqueHashCodeForUninterpretedTerm(Term term) {
	Integer number = this.variableMap
		.get(new UninterpretedTermWrapper(term));
	if (number == null) {
	    number = new Integer(this.variableMap.size());
	    this.variableMap.put(new UninterpretedTermWrapper(term), number);
	}
	return number.intValue();
    }

    /**
     * Build a new copy of t, except that any occurence of an if-then-else term
     * whose if-part equals @param ifPart is replaced by the then-part (if @param
     * part is true) or by the else-part (if @param part is false).
     * 
     * @author gladisch
     */
    private Term replaceIfThenElse(Term t, Term ifPart, boolean part) {
	if (t.arity() == 0) {
	    return t;
	}

	if (ifPart.sort() != Sort.FORMULA) {
	    throw new RuntimeException("Unexpected parameter 2\nParam1=\n"
		    + t.toString() + "\nParam2= (sort:" + ifPart.sort() + ")\n"
		    + ifPart.toString());
	}

	// Base case
	if (t.sub(0) == ifPart) {
	    if (!(t.op() instanceof IfThenElse)) {
		throw new RuntimeException(
			"Unexpected parameter combination. Firs parameter should be an if-then-else term\nParam1=\n"
				+ t.toString()
				+ "\nParam2=\n"
				+ ifPart.toString());
	    }
	    if (part) {
		return replaceIfThenElse(t.sub(1), ifPart, part);
	    } else {
		return replaceIfThenElse(t.sub(2), ifPart, part);
	    }
	}

	// Recursive replacement
	Term[] subs = new Term[t.arity()];
	for (int i = 0; i < t.arity(); i++) {
	    subs[i] = replaceIfThenElse(t.sub(i), ifPart, part);
	}

	// collect bound variables
	final ArrayOfQuantifiableVariable[] vars = new ArrayOfQuantifiableVariable[t
		.arity()];
	for (int i = 0; i < t.arity(); i++) {
	    vars[i] = t.varsBoundHere(i);
	}

	// build the new term
	return tf.createTerm(t.op(), subs, vars, t.javaBlock());
    }

    /**
     * If an if-then-else term is found in t, then the if-condition of the
     * if-then-else is returned. Otherwise null is returned.
     * 
     * @author gladisch
     */
    private Term findIfThenElse(Term t) {
	if ((t.op() instanceof IfThenElse) && t.sort() != Sort.FORMULA) {
	    return t.sub(0);
	}
	for (int i = 0; i < t.arity(); i++) {
	    Term res = findIfThenElse(t.sub(i));
	    if (res != null) {
		return res;
	    }
	}
	return null;
    }

    /**
     * If an division term is found in the formula t, then the term is returned.
     * Otherwise null is returned.
     * 
     * @author mbender
     */
    private Term findDivIForm(Term t) {
	Term sub;
	Term res;
	for (int i = 0; i < t.arity(); i++) {
	    sub = t.sub(i);
	    if (sub.sort() == Sort.FORMULA) {
		if ((res = findDivIForm(sub)) != null) {
		    return res;
		}
	    } else {
		if ((res = findDivITerm(sub)) != null) {
		    return t;
		}
	    }
	}
	return null;
    }

    /**
     * If an division term is found in the term t, then the term is returned.
     * Otherwise null is returned.
     * 
     * @author mbender
     */
    private Term findDivITerm(Term t) {
	if ((t.op().equals(integerLDT.getDiv()))) {
	    return t;
	} else if (!(t.op().name().toString().equals(
		AbstractIntegerLDT.NUMBERS_NAME) || t.arity() == 0)) {
	    Term res;
	    for (int i = 0; i < t.arity(); i++) {
		if ((res = findDivITerm(t.sub(i))) != null) {
		    return res;
		}
	    }
	}
	return null;
    }

    /**
     * Build a new copy of @param term, except that any occurence of the term @param
     * divForm is replaced by a term that equals @param divForm a variable
     * instead of the division. Additionally a term is conjunctivly added to
     * 'define' the value of the introduced variable. This procedure is needed
     * to express the division through a multiplication
     * 
     * @author mbender
     */
    private Term replaceForm(Term form, Term divForm, Term divTerm, Term newVar) {
	boolean isForm = form.equals(divForm);
	final int l = form.arity();
	final Term[] subs = new Term[l];
	final ArrayOfQuantifiableVariable[] qVars = new ArrayOfQuantifiableVariable[l];
	for (int i = 0; i < l; i++) {
	    subs[i] = form.sub(i);
	    if (isForm) {
		subs[i] = replaceTerm(subs[i], divTerm, newVar);
	    } else if (subs[i].sort() == Sort.FORMULA) {
		subs[i] = replaceForm(subs[i], divForm, divTerm, newVar);
	    }
	    qVars[i] = subs[i].varsBoundHere(i);
	}
	return tf.createTerm(form.op(), subs, qVars, form.javaBlock());
    }

    private Term replaceTerm(Term term, Term divTerm, Term newVar) {
	if (term.arity() == 0
		|| term.op().name().toString().equals(
			AbstractIntegerLDT.NUMBERS_NAME)) {
	    return term;
	} else if (term.equals(divTerm)) {
	    return newVar;
	} else {
	    final int l = term.arity();
	    final Term[] subs = new Term[l];
	    final ArrayOfQuantifiableVariable[] qVars = new ArrayOfQuantifiableVariable[l];
	    for (int i = 0; i < l; i++) {
		subs[i] = replaceTerm(term.sub(i), divTerm, newVar);
		qVars[i] = term.varsBoundHere(i);
	    }
	    return tf.createTerm(term.op(), subs, qVars, term.javaBlock());
	}
    }

    private Term createAddConst(Term divTerm, Term newVar) {
	final Term divident = divTerm.sub(0);
	final Term divisor = divTerm.sub(1);
	final Term multip = tf.createFunctionTerm(integerLDT.getMul(), newVar,
		divisor);
	return tf.createEqualityTerm(divident, multip);
    }

    public final StringBuffer pretranslate(Term term,
	    Vector<QuantifiableVariable> quantifiedVars)
	    throws SimplifyException {
	// System.out.println("-Pretranslate");
	// System.out.println(term);
	// replace if-then-else terms
	if (term.sort() == Sort.FORMULA && term.arity() > 0) {
	    // This will be the if-condition of the found if-then-else term
	    Term if_cond = null;
	    while ((if_cond = findIfThenElse(term)) != null) {
		Term term1 = replaceIfThenElse(term, if_cond, true);
		Term term2 = replaceIfThenElse(term, if_cond, false);
		term = tf.createJunctorTerm(Op.AND, tf.createJunctorTerm(
			Op.IMP, if_cond, term1), tf.createJunctorTerm(Op.IMP,
			tf.createJunctorTerm(Op.NOT, if_cond), term2));
	    }
	    Term divForm = null;
	    Term divTerm = null;
	    Term newVar = null;
	    Term addConst = null;
	    // System.out.println("---Term\n" + term);
	    while ((divForm = findDivIForm(term)) != null) {
		// System.out.println("\n");
		// System.out.println("---DivForm\n" + divForm);
		divTerm = findDivITerm(divForm);
		// System.out.println("---divTerm\n" + divTerm);
		newVar = tf.createVariableTerm(new LogicVariable(new Name(
			getUniqueVariableName(divTerm.sort()).toString()),
			divTerm.sort()));
		// System.out.println("---newVar\n" + newVar);
		addConst = createAddConst(divTerm, newVar);
		// System.out.println("---AddConst\n" + addConst);
		term = tf.createJunctorTerm(Op.AND, addConst, replaceForm(term,
			divForm, divTerm, newVar));
		// System.out.println("---ReplaceTerm\n" + term);
	    }
	}
	return translate(term, quantifiedVars);
    }

    /**
     * Translates the given term into "Simplify" input syntax and adds the
     * resulting string to the StringBuffer sb.
     * 
     * @param term
     *            the Term which should be written in Simplify syntax
     * @param quantifiedVars
     *            a Vector containing all variables that have been bound in
     *            super-terms. It is only used for the translation of modulo
     *            terms, but must be looped through until we get there.
     */
    public final StringBuffer translate(Term term,
	    Vector<QuantifiableVariable> quantifiedVars)
	    throws SimplifyException {
	Operator op = term.op();
	if (op == Op.NOT) {
	    return (translateSimpleTerm(term, NOT, quantifiedVars));
	} else if (op == Op.AND) {
	    return (translateSimpleTerm(term, AND, quantifiedVars));
	} else if (op == Op.OR) {
	    return (translateSimpleTerm(term, OR, quantifiedVars));
	} else if (op == Op.IMP) {
	    return (translateSimpleTerm(term, IMP, quantifiedVars));
	} else if (op == Op.EQV) {
	    return (translateSimpleTerm(term, EQV, quantifiedVars));
	} else if (op == Op.EQUALS) {
	    return (translateSimpleTerm(term, EQUALS, quantifiedVars));
	} else if (op == Op.ALL || op == Op.EX) {
	    quantifiersOccur = true;
	    StringBuffer hb = new StringBuffer();
	    Debug.assertTrue(term.arity() == 1);
	    hb.append('(').append(op == Op.ALL ? ALL : EX).append(" (");
	    ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
	    Debug.assertTrue(vars.size() == 1);
	    String v = translateVariable(vars.getQuantifiableVariable(0))
		    .toString();
	    hb.append(v);
	    Vector<QuantifiableVariable> cloneVars = (Vector<QuantifiableVariable>) quantifiedVars
		    .clone();
	    collectQuantifiedVars(cloneVars, term);
	    hb.append(") ");
	    // we now add an implication or conjunction of a type predicate if
	    // the type is
	    // different from int

	    hb.append("(").append(op == Op.ALL ? IMP : AND);
	    Sort sort = vars.getQuantifiableVariable(0).sort();
	    if (isSomeIntegerSort(sort))
		sort = integerSort;
	    hb.append("(" + getUniqueVariableName(sort) + " " + v + " )");
	    addPredicate(getUniqueVariableName(sort).toString(), 1);
	    hb.append(translate(term.sub(0), cloneVars));
	    hb.append("))");

	    return hb;
	} else if (op == Op.TRUE) {
	    return (new StringBuffer(TRUE));
	} else if (op == Op.FALSE) {
	    return (new StringBuffer(FALSE));
	} else if (op instanceof AttributeOp) {
	    return (translateAttributeOpTerm(term, quantifiedVars));
	} else if (op instanceof ProgramMethod) {
	    return (translateSimpleTerm(term, getUniqueVariableName(op)
		    .toString(), quantifiedVars));
	} else if (op instanceof LogicVariable || op instanceof ProgramVariable) {
	    return (translateVariable(op));
	} else if (op instanceof Metavariable) {
	    if (localMetavariables.contains((Metavariable) op)) {
		usedLocalMv.add((Metavariable) op);
	    } else {
		usedGlobalMv.add((Metavariable) op);
	    }
	    return (translateVariable(op));
	} else if (op instanceof ArrayOp) {
	    return (translateSimpleTerm(term, "ArrayOp", quantifiedVars));
	} else if (op instanceof Function) {
	    String name = op.name().toString().intern();
	    if (name.equals("add")) {
		return (translateSimpleTerm(term, PLUS, quantifiedVars));
	    } else if (name.equals("sub")) {
		return (translateSimpleTerm(term, MINUS, quantifiedVars));
	    } else if (name.equals("neg")) {
		// %%: This is not really hygienic
		return (translateUnaryMinus(term, MINUS, quantifiedVars));
	    } else if (name.equals("mul")) {
		return (translateSimpleTerm(term, MULT, quantifiedVars));
	    } else if (name.equals("div")) {
		notes.append(
			"Division encountered which is not "
				+ "supported by Simplify.").append(
			"It is treated as an uninterpreted function.\n");
		return (translateSimpleTerm(term, getUniqueVariableName(op)
			.toString(), quantifiedVars));
	    } else if (name.equals("lt")) {
		return (translateSimpleTerm(term, LT, quantifiedVars));
	    } else if (name.equals("gt")) {
		return (translateSimpleTerm(term, GT, quantifiedVars));
	    } else if (name.equals("leq")) {
		return (translateSimpleTerm(term, LEQ, quantifiedVars));
	    } else if (name.equals("geq")) {
		return (translateSimpleTerm(term, GEQ, quantifiedVars));
	    } else if (name.equals("Z") || name.equals("C")) {
		Debug.assertTrue(term.arity() == 1);

		String res = NumberTranslation.translate(term.sub(0))
			.toString();
		final Sort sort;
		if (isSomeIntegerSort(term.sort()))
		    sort = integerSort;
		else
		    sort = term.sort();
		String ax = "(" + getUniqueVariableName(sort).toString() + " "
			+ res + ")";
		if (!sortAxioms.contains(ax)) {
		    sortAxioms = sortAxioms.prepend(new String[] { ax });
		    addPredicate(getUniqueVariableName(sort).toString(), 1);
		}
		return (new StringBuffer(res));
	    } else if (name.equals("byte_MIN") | name.equals("byte_MAX")
		    | name.equals("byte_RANGE") | name.equals("byte_HALFRANGE")
		    | name.equals("short_MIN") | name.equals("short_MAX")
		    | name.equals("short_RANGE")
		    | name.equals("short_HALFRANGE") | name.equals("int_MIN")
		    | name.equals("int_MAX") | name.equals("int_RANGE")
		    | name.equals("int_HALFRANGE") | name.equals("long_MIN")
		    | name.equals("long_MAX") | name.equals("long_RANGE")
		    | name.equals("long_HALFRANGE")) {
		return (translateSimpleTerm(term, name, quantifiedVars));
	    } else {
		if (term.sort() == Sort.FORMULA) {
		    addPredicate(getUniqueVariableName(op).toString(), op
			    .arity());
		}
		return (translateSimpleTerm(term, getUniqueVariableName(op)
			.toString(), quantifiedVars));
	    }
	} else if ((op instanceof Modality) || (op instanceof IUpdateOperator)
	/* ||(op instanceof IfThenElse) */) {
	    return (uninterpretedTerm(term, true));
	}
	if ((op instanceof IfThenElse)) {
	    if (term.sort() != Sort.FORMULA) {
		throw new RuntimeException(
			"The if-then-else term should have been replaced at this place.\n"
				+ term.toString());
	    } else {
		return translateIfThenElse(term, quantifiedVars);
	    }
	} else {
	    return (translateUnknown(term));
	}
    }

    private final StringBuffer translateIfThenElse(Term term,
	    Vector<QuantifiableVariable> quantifiedVars)
	    throws SimplifyException {
	Term cond = term.sub(0);
	term = tf.createJunctorTerm(Op.AND, tf.createJunctorTerm(Op.IMP, cond,
		term.sub(1)), tf.createJunctorTerm(Op.IMP, tf
		.createJunctorTerm(Op.NOT, cond), term.sub(2)));
	return translate(term, quantifiedVars);
    }

    /**
     * Adds a predicate to the internal set and adds a line to declare the
     * predicate to the declarator stringbuffer.
     * 
     * @param name
     *            The name of the predicate (no KeY representation jas to
     *            exist).
     * @param arity
     *            The arity of the term.
     */
    private final void addPredicate(String name, int arity) {
	if (!predicateSet.contains(name)) {
	    predicateSet.add(name);
	    predicate.append("(DEFPRED (").append(name);
	    for (int i = 0; i < arity; ++i) {
		predicate.append(" x").append(counter++);
	    }
	    predicate.append("))\n");
	}
    }

    /**
     * Just copies the quantified variables of term into quantifiedVars
     * 
     * @param quantifiedVars
     * @param term
     */
    private void collectQuantifiedVars(
	    Vector<QuantifiableVariable> quantifiedVars, Term term) {
	ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
	for (int i = 0; i < vars.size(); ++i) {
	    quantifiedVars.add(vars.getQuantifiableVariable(i));
	}
    }

    /**
     * produces a unique name for the given Variable, enclosed in '|' and with a
     * unique hashcode.
     * 
     * @param op
     *            The variable to get a new name.
     */
    private final StringBuffer getUniqueVariableName(Named op) {
	String name = op.name().toString();
	if (name.indexOf("undef(") != -1) {
	    name = "_undef";
	}
	if (name.indexOf("::") == -1 && name.indexOf(".") == -1
		&& name.indexOf("-") == -1 && !name.startsWith("_")
		&& name.indexOf("[") == -1 && name.indexOf("]") == -1) {
	    return new StringBuffer(name).append("_").append(
		    getUniqueHashCode(op));
	}
	return new StringBuffer("|").append(name).append("_").append(
		getUniqueHashCode(op)).append("|");
    }

    private boolean isSomeIntegerSort(Sort s) {
	if (s == jbyteSort || s == jshortSort || s == jintSort
		|| s == jlongSort || s == jcharSort)
	    return true;
	return false;
    }

    private StringBuffer opNotKnownWarning(Term term) throws SimplifyException {
	logger
		.warn("Warning: unknown operator while translating into Simplify "
			+ "syntax. Translation to Simplify will be stopped here.\n"
			+ "opClass="
			+ term.op().getClass().getName()
			+ ", opName="
			+ term.op().name()
			+ ", sort="
			+ term.sort().name());
	throw new SimplifyException(term.op().name() + " not known by Simplify");
    }

    /**
     * Goes through the collected metavariables and quantifies them with
     * universal-quantifieres if they are global and with existential
     * quantifiers if they are local.
     * 
     * @param s
     *            The StringBuffer the quantifieres shall be pre- and the
     *            trailing parantheses be appended.
     * @returns The modified StringBuffer as a String.
     */
    private String produceClosure(StringBuffer s) {
	StringBuffer tmp = new StringBuffer("(");
	tmp.append(ALL).append(" (");
	for (Iterator<Metavariable> i = usedGlobalMv.iterator(); i.hasNext();) {
	    tmp.append(' ').append(getUniqueVariableName(i.next()));
	}
	tmp.append(")");
	tmp.append("(").append(EX).append(" (");
	for (Iterator<Metavariable> i = usedLocalMv.iterator(); i.hasNext();) {
	    tmp.append(' ').append(getUniqueVariableName(i.next()));
	}
	tmp.append(")\n ");
	tmp.append(s);
	tmp.append("\n))");
	return tmp.toString();
    }

    /**
     * Translates the given ConstrainedFormula into "Simplify" input syntax and
     * adds the resulting string to the StringBuffer sb.
     * 
     * @param cf
     *            the ConstrainedFormula which should be written in Simplify
     *            syntax
     */
    private final StringBuffer translate(ConstrainedFormula cf,
	    boolean lightWeight) throws SimplifyException {
	StringBuffer hb = new StringBuffer();
	if (constraintSet.used(cf)) {

	    SyntacticalReplaceVisitor srVisitor = new SyntacticalReplaceVisitor(
		    constraintSet.getChosenConstraint());
	    cf.formula().execPostOrder(srVisitor);
	    Term t = srVisitor.getTerm();
	    Operator op = t.op();
	    if (!lightWeight || !(op instanceof Modality)
		    && !(op instanceof IUpdateOperator)
		    && !(op instanceof IfThenElse) && op != Op.ALL
		    && op != Op.EX) {
		hb.append(pretranslate(t, new Vector<QuantifiableVariable>()));
	    }
	}
	return hb;
    }

    /**
     * Translates the given Semisequent into "Simplify" input syntax and adds
     * the resulting string to the StringBuffer sb.
     * 
     * @param semi
     *            the SemiSequent which should be written in Simplify syntax
     */
    private final StringBuffer translate(Semisequent semi, int skolemization,
	    boolean lightWeight) throws SimplifyException {
	StringBuffer hb = new StringBuffer();
	hb.append('(');
	if (skolemization == ANTECEDENT) {
	    hb.append(AND);
	} else {
	    hb.append(OR);
	}
	for (int i = 0; i < semi.size(); ++i) {
	    hb.append(' ');
	    hb.append(translate(semi.get(i), lightWeight));
	}
	hb.append(')');
	return hb;
    }

    /**
     * Translates the given sequent into "Simplify" input syntax and adds the
     * resulting string to the StringBuffer sb.
     * 
     * @param sequent
     *            the Sequent which should be written in Simplify syntax
     */
    private final StringBuffer translate(Sequent sequent, boolean lightWeight)
	    throws SimplifyException {
	// computeModuloConstraints(sequent);
	StringBuffer hb = new StringBuffer();
	hb.append('(').append(IMP).append(' ');
	hb.append(translate(sequent.antecedent(), ANTECEDENT, lightWeight));
	hb.append("\n");
	hb.append(translate(sequent.succedent(), SUCCEDENT, lightWeight));
	hb.append(')');

	if (!sortAxioms.isEmpty() && quantifiersOccur) {
	    String sar[] = sortAxioms.toArray();
	    String axioms = sar[0];
	    for (int i = 1; i < sar.length; i++) {
		axioms = "(" + AND + " " + axioms + " " + sar[i] + ")";
	    }
	    hb.insert(0, "(" + IMP + " " + axioms);
	    hb.append(')');
	}

	return hb;
    }

    /**
     * Takes an AttributeOp and translates it into the Simplify syntax.
     * 
     * @param term
     *            The term to be converted.
     * @param quantifiedVars
     *            a Vector containing all variables that have been bound in
     *            super-terms. It is only used for the translation of modulo
     *            terms, but must be looped through until we get there.
     */
    private final StringBuffer translateAttributeOpTerm(Term term,
	    Vector<QuantifiableVariable> quantifiedVars)
	    throws SimplifyException {
	StringBuffer hb = new StringBuffer();
	if (logger.isDebugEnabled()) {
	    logger.debug("opClass=" + term.op().getClass().getName()
		    + ", opName=" + term.op().name() + ", sort="
		    + term.sort().name());
	}

	hb.append(getUniqueVariableName(term.op()));
	Debug.assertTrue(term.varsBoundHere(0).size() == 0);
	hb.append(' ');
	hb.append(translate(term.sub(0), quantifiedVars));
	hb.insert(0, '(');
	hb.append(')');

	final Sort sort;
	if (isSomeIntegerSort(term.sort()))
	    sort = integerSort;
	else
	    sort = term.sort();
	String ax = "(" + getUniqueVariableName(sort).toString() + " " + hb
		+ ")";
	if (!sortAxioms.contains(ax)) {
	    sortAxioms = sortAxioms.prepend(new String[] { ax });
	    addPredicate(getUniqueVariableName(sort).toString(), 1);
	}

	return hb;
    }

    /**
     * Takes a term and translates it with its argument in the Simplify syntax.
     * 
     * @param term
     *            The term to be converted.
     * @param name
     *            The name that should be used for the term (should be unique,
     *            it should be taken care of that somewhere else (if desired)).
     * @param quantifiedVars
     *            a Vector containing all variables that have been bound in
     *            super-terms. It is only used for the translation of modulo
     *            terms, but must be looped through until we get there.
     */
    private final StringBuffer translateSimpleTerm(Term term, String name,
	    Vector<QuantifiableVariable> quantifiedVars)
	    throws SimplifyException {
	StringBuffer hb = new StringBuffer();
	hb.append('(').append(name);
	StringBuffer res = null;
	for (int i = 0; i < term.arity(); ++i) {
	    Debug.assertTrue(term.varsBoundHere(i).size() == 0);
	    hb.append(' ');
	    res = translate(term.sub(i), quantifiedVars);
	    if (res != null && term.sub(i).sort() != Sort.FORMULA) {
		final Sort sort;
		if (isSomeIntegerSort(term.sub(i).sort()))
		    sort = integerSort;
		else
		    sort = term.sub(i).sort();
		String ax = "(" + getUniqueVariableName(sort).toString() + " "
			+ res + ")";
		if (!sortAxioms.contains(ax)) {
		    sortAxioms = sortAxioms.prepend(new String[] { ax });
		    addPredicate(getUniqueVariableName(sort).toString(), 1);
		}
	    }

	    hb.append(res);
	}
	hb.append(')');

	// add sort axioms
	return hb;
    }

    /**
     * Translates the unary minus ~m into a "0 -" construct. Could be solved
     * better with a newly created term!!!
     * 
     * @param term
     *            The term to be converted.
     * @param name
     *            The name that should be used for the term (should be unique,
     *            it should be taken care of that somewhere else (if desired)).
     * @param quantifiedVars
     *            a Vector containing all variables that have been bound in
     *            super-terms. It is only used for the translation of modulo
     *            terms, but must be looped through until we get there.
     */
    private final StringBuffer translateUnaryMinus(Term term, String name,
	    Vector<QuantifiableVariable> quantifiedVars)
	    throws SimplifyException {
	StringBuffer hb = new StringBuffer();
	hb.append('(').append(name).append(" 0");
	hb.append(translate(term.sub(0), quantifiedVars));
	hb.append(')');
	return hb;
    }

    /**
     * Takes care of sequent tree parts that were not matched in translate(term,
     * skolemization). In this class it just produces a warning, nothing more.
     * It is provided as a hook for subclasses.
     * 
     * @param term
     *            The Term given to translate
     * @throws SimplifyException
     */
    private StringBuffer translateUnknown(Term term) throws SimplifyException {
	return (opNotKnownWarning(term));
    }

    /**
     * Used to give a variable (program, logic, meta) a unique name.
     * 
     * @param op
     *            The variable to be translated/renamed.
     */
    private final StringBuffer translateVariable(Operator op) {
	StringBuffer res = getUniqueVariableName(op);
	if (op instanceof ProgramVariable || op instanceof Metavariable) {
	    final Sort sort;
	    if (isSomeIntegerSort(op.sort(null)))
		sort = integerSort;
	    else
		sort = op.sort(null);
	    String ax = "(" + getUniqueVariableName(sort).toString() + " "
		    + res + ")";
	    if (!sortAxioms.contains(ax)) {
		sortAxioms = sortAxioms.prepend(new String[] { ax });
		addPredicate(getUniqueVariableName(sort).toString(), 1);
	    }
	}
	return res;
    }

    private final StringBuffer uninterpretedTerm(Term term, boolean modRenaming) {
	if (cacheForUninterpretedSymbols.containsKey(term))
	    return cacheForUninterpretedSymbols.get(term);
	StringBuffer hb = new StringBuffer();
	StringBuffer temp = new StringBuffer();
	temp.append('|').append(term.op().name()).append('_');
	if (modRenaming) {
	    temp.append(getUniqueHashCodeForUninterpretedTerm(term));
	} else {
	    temp.append(getUniqueHashCode(term));
	}
	temp.append('|');
	hb.append(temp);
	IteratorOfQuantifiableVariable i;
	for (i = term.freeVars().iterator(); i.hasNext();) {
	    hb.append(' ');
	    hb.append(translateVariable(i.next()));
	}

	if (term.sort() != Sort.FORMULA) {
	    String ax;
	    final Sort sort;
	    if (isSomeIntegerSort(term.sort()))
		sort = integerSort;
	    else
		sort = term.sort();
	    if (term.arity() > 0)
		ax = "(" + getUniqueVariableName(sort).toString() + " (" + hb
			+ "))";
	    else
		ax = "(" + getUniqueVariableName(sort).toString() + " " + hb
			+ ")";
	    if (!sortAxioms.contains(ax)) {
		sortAxioms = sortAxioms.prepend(new String[] { ax });
		addPredicate(getUniqueVariableName(sort).toString(), 1);
	    }
	}

	hb.insert(0, '(');
	hb.append(')');

	if (term.sort() == Sort.FORMULA)
	    addPredicate(temp.toString(), term.freeVars().size());
	cacheForUninterpretedSymbols.put(term, hb);
	return hb;
    }

}
