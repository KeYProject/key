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
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.util.Debug;


/**
 * 
 * @author daniels
 *
 * The class responsible for converting a sequent into the Simplify input language.
 * It is public because ASM-KeY inherits form it to provide a version suppporting
 * asm operators.
 */
public class SimplifyTranslation extends DecProcTranslation { 

    private HashMap cacheForUninterpretedSymbols = null;
    private ListOfString sortAxioms = SLListOfString.EMPTY_LIST;
    private boolean quantifiersOccur=false;   
    private Sort jbyteSort;
    private Sort jshortSort;
    private Sort jintSort;
    private Sort jlongSort;
    private Sort jcharSort;
    private Sort integerSort;
    private static long counter = 0;
	
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
	public SimplifyTranslation(Sequent sequent, ConstraintSet cs,
				   SetOfMetavariable localmv, 
				   Services services,
				   boolean lightWeight) 
	    throws SimplifyException {
		super(sequent, cs, localmv, services);                
                jbyteSort = services.getTypeConverter().getByteLDT().targetSort();
                jshortSort = services.getTypeConverter().getShortLDT().targetSort();
                jintSort = services.getTypeConverter().getIntLDT().targetSort();
                jlongSort = services.getTypeConverter().getLongLDT().targetSort();
                jcharSort = services.getTypeConverter().getCharLDT().targetSort();
                integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
		cacheForUninterpretedSymbols = new HashMap();
		StringBuffer hb = translate(sequent, lightWeight);
		text = predicate.toString() + produceClosure(hb);
		logger.info("SimplifyTranslation:\n" + text);
		if (notes.length() > 0) {
			logger.info(notes);
		}
	}

	public SimplifyTranslation(Sequent sequent, ConstraintSet cs,
				   SetOfMetavariable localmv, 
				   Services services) 
	    throws SimplifyException {
	    this(sequent, cs, localmv, services, false);
	}

    /**
     * For translating only terms and not complete sequents.
     */
    public SimplifyTranslation(Services s) throws SimplifyException{
        this(null, null, null, s, false);
    }

	/**
	 * Goes through the collected metavariables and quantifies them with 
	 * universal-quantifieres if they are global and with existential 
	 * quantifiers if they are local.
	 * @param s The StringBuffer the quantifieres shall be pre- and 
	 * the trailing parantheses be appended.
	 * @returns The modified StringBuffer as a String.
	 */
	protected String produceClosure(StringBuffer s) {
		StringBuffer tmp = new StringBuffer("(");
		tmp.append(DecisionProcedureSimplifyOp.ALL).append(" (");
		for (Iterator i = usedGlobalMv.iterator(); i.hasNext();) {
			tmp.append(' ').append(
					getUniqueVariableName((Metavariable) i.next()));
		}
		tmp.append(")");
		tmp.append("(").append(DecisionProcedureSimplifyOp.EX).append(" (");
		for (Iterator i = usedLocalMv.iterator(); i.hasNext();) {
			tmp.append(' ').append(
					getUniqueVariableName((Operator) i.next()));
		}
		tmp.append(")\n ");
		tmp.append(s);
		tmp.append("\n))");
		return tmp.toString();
	}

    protected final StringBuffer translate(Sequent sequent)
	throws SimplifyException {
	return translate(sequent, false);
    }

	/**
	 * Translates the given sequent into "Simplify" input syntax and adds the
	 * resulting string to the StringBuffer sb.
	 * 
	 * @param sequent
	 *           the Sequent which should be written in Simplify syntax
	 */
	protected final StringBuffer translate(Sequent sequent, 
					       boolean lightWeight)
			throws SimplifyException {
	    //		computeModuloConstraints(sequent);
		StringBuffer hb = new StringBuffer();
		hb.append('(').append(DecisionProcedureSimplifyOp.IMP).append(' ');
		hb.append(translate(sequent.antecedent(), ANTECEDENT,
				    lightWeight));
		hb.append("\n");
		hb.append(translate(sequent.succedent(), SUCCEDENT,
				    lightWeight));
		hb.append(')');

		if (!sortAxioms.isEmpty() && quantifiersOccur) {
		    String sar[] = sortAxioms.toArray();
		    String axioms=sar[0];
		    for (int i=1; i<sar.length; i++) {
			axioms="("+DecisionProcedureSimplifyOp.AND+" "+axioms+" "+sar[i]+")";
		    }
		    hb.insert(0, "("+DecisionProcedureSimplifyOp.IMP+" "+axioms);
		    hb.append(')');
		    //System.out.println(axioms);
		}

		return hb;
	}

	protected final StringBuffer translate(Semisequent ss, 
					       int skolemization)
	    throws SimplifyException {
	    return translate(ss, skolemization, false);
	}

	/**
	 * Translates the given Semisequent into "Simplify" input syntax and adds
	 * the resulting string to the StringBuffer sb.
	 * 
	 * @param semi
	 *           the SemiSequent which should be written in Simplify syntax
	 */
	protected final StringBuffer translate(Semisequent semi, 
					       int skolemization,
					       boolean lightWeight)
			throws SimplifyException {
		StringBuffer hb = new StringBuffer();
		hb.append('(');
		if (skolemization == ANTECEDENT) {
			hb.append(DecisionProcedureSimplifyOp.AND);
		} else {
			hb.append(DecisionProcedureSimplifyOp.OR);
		}
		for (int i = 0; i < semi.size(); ++i) {
			hb.append(' ');
			hb.append(translate(semi.get(i), lightWeight));
		}
// 		if (skolemization == ANTECEDENT) {
// 			hb.append(' ');
// 			hb.append(DecisionProcedureSimplifyOp.LIMIT_FACTS);
// 			hb.append('\n').append(translate(moduloConjoin(), new Vector()));
// 		}
		hb.append(')');
		return hb;
	}
	/**
	 * Translates the given ConstrainedFormula into "Simplify" input syntax and
	 * adds the resulting string to the StringBuffer sb.
	 * 
	 * @param cf
	 *           the ConstrainedFormula which should be written in Simplify
	 *           syntax
	 */
	protected final StringBuffer translate(ConstrainedFormula cf, 
					       boolean lightWeight)
	    throws SimplifyException {
	    StringBuffer hb = new StringBuffer();
	    if (constraintSet.used(cf)) {
		SyntacticalReplaceVisitor srVisitor = 
		    new SyntacticalReplaceVisitor(
			constraintSet.chosenConstraint());
		cf.formula().execPostOrder(srVisitor);
		Term t = srVisitor.getTerm();
		Operator op = t.op();
		if (!lightWeight || !(op instanceof Modality)
		    && !(op instanceof IUpdateOperator)
		    && !(op instanceof IfThenElse)
		    && op != Op.ALL
		    && op != Op.EX){	
		    hb.append(translate(t, new Vector()));
		}
	    }
	    return hb;
	}
	/**
	 * Translates the given term into "Simplify" input syntax and adds the
	 * resulting string to the StringBuffer sb.
	 * 
	 * @param term
	 *        the Term which should be written in Simplify syntax
	 * @param quantifiedVars
	 *           a Vector containing all variables that have been bound in
	 *           super-terms. It is only used for the translation of modulo
	 *           terms, but must be looped through until we get there.
	 */
	public final StringBuffer translate(Term term, Vector quantifiedVars) throws SimplifyException {
		Operator op = term.op();
		if (op == Op.NOT) {
			return (translateSimpleTerm(term, DecisionProcedureSimplifyOp.NOT, quantifiedVars));
		} else if (op == Op.AND) {
			return (translateSimpleTerm(term, DecisionProcedureSimplifyOp.AND, quantifiedVars));
		} else if (op == Op.OR) {
			return (translateSimpleTerm(term, DecisionProcedureSimplifyOp.OR, quantifiedVars));
		} else if (op == Op.IMP) {
			return (translateSimpleTerm(term, DecisionProcedureSimplifyOp.IMP, quantifiedVars));
		} else if (op == Op.EQV) {
			return (translateSimpleTerm(term, DecisionProcedureSimplifyOp.EQV, quantifiedVars));
		} else if (op == Op.EQUALS) {		    
			return (translateSimpleTerm(term,
						    DecisionProcedureSimplifyOp.EQUALS, quantifiedVars));
		} else if (op == Op.ALL || op == Op.EX) {
		    quantifiersOccur = true;
			StringBuffer hb = new StringBuffer();
			Debug.assertTrue(term.arity() == 1);
			hb.append('(').append(
					op == Op.ALL
							? DecisionProcedureSimplifyOp.ALL
							: DecisionProcedureSimplifyOp.EX).append(" (");
			ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
			Debug.assertTrue(vars.size()==1);
			String v = translateVariable(vars.getQuantifiableVariable(0)).toString();
			hb.append(v);
			Vector cloneVars = (Vector)quantifiedVars.clone(); 
			collectQuantifiedVars(cloneVars, term);
			hb.append(") ");
			// we now add an implication or conjunction of a type predicate if the type is 
			// different from int
			
			hb.append("(").append(
					      op == Op.ALL
					      ? DecisionProcedureSimplifyOp.IMP
					      : DecisionProcedureSimplifyOp.AND);
                        Sort sort = vars.getQuantifiableVariable(0).sort();
                        if (isSomeIntegerSort(sort)) 
			    sort = integerSort;
			hb.append("("+getUniqueVariableName(sort)+" "+v+" )");
			addPredicate(getUniqueVariableName(sort).toString(),1);
			hb.append(translate(term.sub(0), cloneVars));			  
			hb.append("))");
			
			return hb;
		} else if (op == Op.TRUE) {
			return (new StringBuffer(DecisionProcedureSimplifyOp.TRUE));
		} else if (op == Op.FALSE) {
			return (new StringBuffer(DecisionProcedureSimplifyOp.FALSE));
		} else if (op instanceof AttributeOp) {
			return (translateAttributeOpTerm(term, quantifiedVars));
		} else if (op instanceof ProgramMethod) {
			return (translateSimpleTerm(term, getUniqueVariableName(op)
					.toString(), quantifiedVars));
		} else if (op instanceof LogicVariable || op instanceof ProgramVariable) {
			return (translateVariable(op));
		} else if (op instanceof Metavariable) {
			if (localMetavariables.contains((Metavariable) op)) {
				usedLocalMv.add(op);
			} else {
				usedGlobalMv.add(op);
			}
			return (translateVariable(op));
		} else if (op instanceof ArrayOp) {
			return (translateSimpleTerm(term, "ArrayOp", quantifiedVars));
		} else if (op instanceof Function) {
			String name = op.name().toString().intern();
			if (name.equals("add")) {
				return (translateSimpleTerm(term,
						DecisionProcedureSimplifyOp.PLUS, quantifiedVars));
			} else if (name.equals("sub")) {
				return (translateSimpleTerm(term,
						DecisionProcedureSimplifyOp.MINUS, quantifiedVars));
			} else if (name.equals("neg")) {
				//%%: This is not really hygienic
				return (translateUnaryMinus(term,
						DecisionProcedureSimplifyOp.MINUS, quantifiedVars));
			} else if (name.equals("mul")) {
				return (translateSimpleTerm(term,
						DecisionProcedureSimplifyOp.MULT, quantifiedVars));
			} else if (name.equals("div")) {
				notes.append(
						"Division encountered which is not "
								+ "supported by Simplify.").append(
						"It is treated as an uninterpreted function.\n");
				return (translateSimpleTerm(term, getUniqueVariableName(op)
						.toString(), quantifiedVars));
				//			} 
				// else if (name.equals("mod")) {
				// 				Term tt = translateModulo(term, quantifiedVars);
				// 				if (tt == null) {
				// 					return uninterpretedTerm(term, true);
				// 				} else {
				// 					return translate(tt, quantifiedVars);
				// 				}
			} else if (name.equals("lt")) {
				return (translateSimpleTerm(term,
						DecisionProcedureSimplifyOp.LT, quantifiedVars));
			} else if (name.equals("gt")) {
				return (translateSimpleTerm(term,
						DecisionProcedureSimplifyOp.GT, quantifiedVars));
			} else if (name.equals("leq")) {
				return (translateSimpleTerm(term,
						DecisionProcedureSimplifyOp.LEQ, quantifiedVars));
			} else if (name.equals("geq")) {
				return (translateSimpleTerm(term,
						DecisionProcedureSimplifyOp.GEQ, quantifiedVars));
			} else if (name.equals("Z") || name.equals("C")) {
				Debug.assertTrue(term.arity() == 1);

				String res = NumberTranslation.translate(term.sub(0)).toString();
                                final Sort sort;
                                if (isSomeIntegerSort(term.sort())) 
                                        sort = integerSort;
                                else
                                        sort = term.sort();                                
                                String ax = "("+getUniqueVariableName(sort).toString()+" "+res+")";
				if (!sortAxioms.contains(ax)) {
				    sortAxioms = sortAxioms.prepend(new String[]{ax});                                    
				    addPredicate(getUniqueVariableName(sort).toString(),1);                                                                        
				}
				return (new StringBuffer(res));
/* 
// it's sick but if you need to give a demo...
                        } else if (name.equals("short_MIN")) {
                            return new StringBuffer("-32768");
                        } else if (name.equals("short_MAX")) {
                            return new StringBuffer("32767");
                        } else if (name.equals("int_MIN")) {
                            return new StringBuffer("-500000");
                        } else if (name.equals("int_MAX")) {
                            return new StringBuffer("500000");
*/
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
		} else if ((op instanceof Modality)
				|| (op instanceof IUpdateOperator)
                                || (op instanceof IfThenElse)) {
			return (uninterpretedTerm(term, true));
		} else {
			return (translateUnknown(term));
		}
	}
	/**
	 * Takes care of sequent tree parts that were not matched in translate(term,
	 * skolemization). In this class it just produces a warning, nothing more.
	 * It is provided as a hook for subclasses.
	 * 
	 * @param term
	 *           The Term given to translate
	 * @throws SimplifyException
	 */
	protected StringBuffer translateUnknown(Term term) throws SimplifyException {
		return (opNotKnownWarning(term));
	}
	protected StringBuffer opNotKnownWarning(Term term)
			throws SimplifyException {
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
	 * Used to give a variable (program, logic, meta) a unique name.
	 * 
	 * @param op
	 *           The variable to be translated/renamed.
	 */
	protected final StringBuffer translateVariable(Operator op) {
	    StringBuffer res = getUniqueVariableName(op);
	    if (op instanceof ProgramVariable || op instanceof Metavariable) {
                final Sort sort;
                if (isSomeIntegerSort(op.sort(null))) 
                        sort = integerSort;
                else
                        sort = op.sort(null);
		String ax = "("+getUniqueVariableName(sort).toString()+" "+res+")";
		if (!sortAxioms.contains(ax)) {
		    sortAxioms = sortAxioms.prepend(new String[]{ax});                                                       
                    addPredicate(getUniqueVariableName(sort).toString(),1);  		 			
		}
	    }
	    return res;
	}
	/**
	 * produces a unique name for the given Variable, enclosed in '|' and with a
	 * unique hashcode.
	 * 
	 * @param op
	 *           The variable to get a new name.
	 */
	protected final StringBuffer getUniqueVariableName(Named op) {
	    String name = op.name().toString();
	    if(name.indexOf("undef(") != -1){
		name = "_undef";
	    }
	    if(name.indexOf("::")==-1 && name.indexOf(".")==-1 && 
	       name.indexOf("-")==-1 && !name.startsWith("_") &&
               name.indexOf("[")==-1 && name.indexOf("]")==-1){
		return new StringBuffer(name).
		    append("_").append(getUniqueHashCode(op));
	    }
	    return new StringBuffer("|").
		append(name).
		append("_").append(getUniqueHashCode(op)).append("|");
	}
	
	protected final StringBuffer uninterpretedTerm(Term term,
			boolean modRenaming) {
	    if (cacheForUninterpretedSymbols.containsKey(term))
		return (StringBuffer)cacheForUninterpretedSymbols.get(term);
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
		    ax = "("+getUniqueVariableName(sort).toString()+" ("+hb+"))";
		else
		    ax = "("+getUniqueVariableName(sort).toString()+" "+hb+")";
		if (!sortAxioms.contains(ax)) {
		    sortAxioms = sortAxioms.prepend(new String[]{ax});                                                        
                    addPredicate(getUniqueVariableName(sort).toString(),1);  		    
		}
	    }

	    hb.insert(0,'(');
	    hb.append(')');

	    if (term.sort() == Sort.FORMULA)
		addPredicate(temp.toString(), term.freeVars().size());
	    cacheForUninterpretedSymbols.put(term, hb);
	    return hb;
	}
    /**
     * Takes a term and translates it with its argument in the Simplify syntax.
     * 
     * @param term
     *           The term to be converted.
     * @param name
     *           The name that should be used for the term (should be unique,
     *           it should be taken care of that somewhere else (if desired)).
     * @param quantifiedVars
     *           a Vector containing all variables that have been bound in
     *           super-terms. It is only used for the translation of modulo
     *           terms, but must be looped through until we get there.
     */
    protected final StringBuffer translateSimpleTerm(Term term, String name, Vector quantifiedVars)
	throws SimplifyException {
	StringBuffer hb = new StringBuffer();
	hb.append('(').append(name);
	StringBuffer res = null;
	for (int i = 0; i < term.arity(); ++i) {
	    Debug.assertTrue(term.varsBoundHere(i).size() == 0);
	    hb.append(' ');
	    res = translate(term.sub(i), quantifiedVars);
	    if (res!=null && term.sub(i).sort()!=Sort.FORMULA) {
                final Sort sort;
                if (isSomeIntegerSort(term.sub(i).sort())) 
                        sort = integerSort;
                else
                        sort = term.sub(i).sort();
		String ax = "("+getUniqueVariableName(sort).toString()+" "+res+")";
		if (!sortAxioms.contains(ax)) {
		    sortAxioms = sortAxioms.prepend(new String[]{ax});                                                        
                    addPredicate(getUniqueVariableName(sort).toString(),1);		    
		}
	    }
	    
	    hb.append(res);
	}
	hb.append(')');

	// add sort axioms
	return hb;
    }
    /**
     * Takes an AttributeOp and translates it into the Simplify syntax.
     * 
     * @param term
     *           The term to be converted.
     * @param quantifiedVars
     *           a Vector containing all variables that have been bound in
     *           super-terms. It is only used for the translation of modulo
     *           terms, but must be looped through until we get there.
     */
    protected final StringBuffer translateAttributeOpTerm(Term term, Vector quantifiedVars)
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
	hb.insert(0,'(');
	hb.append(')');	

        final Sort sort;
        if (isSomeIntegerSort(term.sort())) 
                sort = integerSort;
        else
                sort = term.sort();
	String ax = "("+getUniqueVariableName(sort).toString()+" "+hb+")";
	if (!sortAxioms.contains(ax)) {
	    sortAxioms = sortAxioms.prepend(new String[]{ax});                                                
            addPredicate(getUniqueVariableName(sort).toString(),1);	    
	}

	return hb;
    }
    /**
     * Translates the unary minus ~m into a "0 -" construct. Could be solved
     * better with a newly created term!!!
     * 
     * @param term
     *           The term to be converted.
     * @param name
     *           The name that should be used for the term (should be unique,
     *           it should be taken care of that somewhere else (if desired)).
     * @param quantifiedVars
     *           a Vector containing all variables that have been bound in
     *           super-terms. It is only used for the translation of modulo
     *           terms, but must be looped through until we get there.
     */
    protected final StringBuffer translateUnaryMinus(Term term, String name, Vector quantifiedVars)
	throws SimplifyException {
	StringBuffer hb = new StringBuffer();
	hb.append('(').append(name).append(" 0");
	hb.append(translate(term.sub(0), quantifiedVars));
	hb.append(')');
	return hb;
    }
    
    /**
     * Adds a predicate to the internal set and adds a line to declare the
     * predicate to the declarator stringbuffer.
     * 
     * @param name
     *           The name of the predicate (no KeY representation jas to
     *           exist).
     * @param arity
     *           The arity of the term.
     */
    protected final void addPredicate(String name, int arity) {
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
     * For some terms (AttributeOps) the order in KeY is different than the
     * order of the user or Simplify expects.
     * 
     * @return the simplified version of the Term t in reversed order
     * @param t
     *           the Term which should be written in Simplify syntax, but in
     *           reverse order compared to the internal order in KeY
     */
    protected final StringBuffer printlastfirst(Term t) {
	StringBuffer sbuff = new StringBuffer();
	if (t.op().arity() > 0) {
	    Debug.assertTrue(t.op().arity() == 1);
	    sbuff.append(printlastfirst(t.sub(0)));
	    //sbuff.append('.');
	}
	sbuff.append(t.op().name()).append("\\|").append(
							 getUniqueHashCode(t.op()));
	return sbuff;
    }
    
    
    static Logger logger = Logger.getLogger(SimplifyTranslation.class.getName());
    
    
    /** 
     * Used just to be called from DecProcTranslation
     * @see de.uka.ilkd.key.proof.decproc.DecProcTranslation#translate(Semisequent, int)
     */
    protected final StringBuffer translate(Term term, int skolemization, Vector quantifiedVars) throws SimplifyException {
	return translate(term, quantifiedVars);
    }
    
    private boolean isSomeIntegerSort(Sort s) {
        if (s == jbyteSort ||
                s == jshortSort ||
                s == jintSort ||
                s == jlongSort ||
                s == jcharSort )
            return true;
        return false;
    }
}
