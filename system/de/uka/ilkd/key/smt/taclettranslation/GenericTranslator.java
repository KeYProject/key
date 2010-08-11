// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.CastFunctionSymbol;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.conditions.TypeComparisionCondition;

class GenericTranslator {

    // only for testing.
    private boolean appendGenericTerm = false;
    // private HashSet<GenericSort> usedGenericSorts;
    private VariablePool pool;
    private Services services;
    private ArrayList<TranslationListener> listener = new ArrayList<TranslationListener>();

    GenericTranslator(VariablePool pool) {
	this.pool = pool;
    }

    /**
     * Translates generic variables.
     * 
     * @param currentTerm
     * @param genericSorts
     * @param sorts
     * @return
     * @throws IllegalTacletException
     */
    public Collection<Term> translate(Term term, ImmutableSet<Sort> sorts, Taclet t,
	    TacletConditions conditions, Services services, int maxGeneric)
	    throws IllegalTacletException {
	this.services = services;
	ImmutableList<Term> list = instantiateGeneric(term,
	        AbstractTacletTranslator.collectGenerics(term), sorts, t, conditions, maxGeneric);
	Collection<Term> result = new LinkedList<Term>();
	if (list == null){
	    result.add(term);
	    return result;
	}
	    

	if (list.isEmpty()) {
	    throw new IllegalTacletException(
		    "Can not instantiate generic variables"
		            + " because there are not enough different sorts.");
	}

	
	if (list.size() > 0) {
	    for (Term gt : list) {
		result.add(AbstractTacletTranslator.quantifyTerm(gt));

	    }
	    if (appendGenericTerm) {
		result.add(term);
	    }
	}

	return result;

	// return
	// instantiateGeneric(term,collectGenerics(term),sorts,t,conditions);
    }

    /**
     * Instantiates all variables of a generic sort with logic variables. The
     * logic variable has the same name with the prefix [sort]__
     * 
     * @param term
     * @param generic
     *            the generic sort that should be instantiated.
     * @param instantiation
     *            the instantiation sort.
     * @return returns the new term with instantiated variables. If
     *         <code>term</code> can not be instantiated the method returns
     *         <code>null</code>, e.g. this can occur, when <code>term</code> is
     *         of type {@link SortDependingFunction} and
     *         <code>instantiation</code> is of type {@link PrimitiveSort}.
     */

    private Term instantiateGeneric(Term term, GenericSort generic,
	    Sort instantiation, Taclet t) throws IllegalArgumentException,
	    IllegalTacletException {
	ImmutableArray<QuantifiableVariable> variables[] = new ImmutableArray[term
	        .arity()];
	Term[] subTerms = new Term[term.arity()];
	for (int i = 0; i < term.arity(); i++) {
	    subTerms[i] = instantiateGeneric(term.sub(i), generic,
		    instantiation, t);
	    if (subTerms[i] == null) {
		return null;
	    }
	    variables[i] = subTerms[i].varsBoundHere(i);
	}

	if (term.sort().equals(generic)) {

	    if (term.op() instanceof LogicVariable) {
		TermBuilder tb = TermBuilder.DF;
		term = tb.var(pool.getInstantiationOfLogicVar(instantiation,
		        (LogicVariable) term.op()));
	    } else if (term.op() instanceof SchemaVariable) {
		if (((SchemaVariable) term.op()).isTermSV()) {
		    term = TermBuilder.DF.var(pool.getInstantiationOfLogicVar(
			    instantiation, pool.getLogicVariable(term.op()
			            .name(), term.sort())));
		}

	    } else if (term.op() instanceof CastFunctionSymbol) {
		term = TermFactory.DEFAULT.createCastTerm(
		        (AbstractSort) instantiation, subTerms[0]);
	    }

	}

	if (term.op() instanceof SortDependingFunction) {

	    SortDependingFunction func = (SortDependingFunction) term.op();
	    try { // Try block is necessary because there are some taclets
		// that should have isReference-Condition, but they don't
		// have the condition.

		if (func.getSortDependingOn().equals(generic)) {
		    term = TermFactory.DEFAULT
			    .createFunctionTerm(
			            (SortDependingFunction) func
			                    .getInstanceFor((SortDefiningSymbols) instantiation),
			            subTerms);
		}
	    } catch (IllegalArgumentException e) {
		for (TranslationListener l : listener) {
		    if (l.eventInstantiationFailure(generic, instantiation, t,
			    term))
			throw e;
		}
		return null;
	    }
	}

	if (term.op() instanceof Quantifier) {
	    QuantifiableVariable[] copy = new QuantifiableVariable[term
		    .varsBoundHere(0).size()];
	    int i = 0;

	    for (QuantifiableVariable var : term.varsBoundHere(0)) {
		copy[i] = var;
		if (copy[i].sort() instanceof GenericSort) {
		    copy[i] = pool.getLogicVariable(copy[i].name(),
			    instantiation);
		}

		i++;
	    }
	    if ((term.op()).equals(Quantifier.ALL)) {
		term = TermBuilder.DF.all(copy, subTerms[0]);
	    }
	    if ((term.op()).equals(Quantifier.EX)) {
		term = TermBuilder.DF.ex(copy, subTerms[0]);
	    }

	}else {
	    term = TermFactory.DEFAULT.createTerm(term.op(), subTerms,
		    variables, JavaBlock.EMPTY_JAVABLOCK);
	}
	return term;

    }

    /**
     * Tests sort of its instantiation ability.
     * 
     * @param sort
     *            sort to be tested.
     * @return <code>true</code> if can be instantiated, otherwise
     *         <code>false</code>
     */
    private boolean doInstantiation(GenericSort generic, Sort inst,
	    TacletConditions conditions) {

	return !((inst instanceof GenericSort)
	        || (inst.equals(Sort.ANY))
	        || (conditions.containsIsReferenceCondition(generic) > 0 && !AbstractTacletTranslator
	                .isReferenceSort(inst))
	        || (conditions.containsNotAbstractInterfaceCondition(generic) && AbstractTacletTranslator
	                .isAbstractOrInterface(inst)) || (conditions
	        .containsAbstractInterfaceCondition(generic) && !AbstractTacletTranslator
	        .isAbstractOrInterface(inst)));
    }



    /**
     * Instantiates generic variables of the term. It instantiates the variables
     * using all possibilities.
     * 
     * @param term
     *            the term to be instantiated.
     * @param genericSorts
     *            the generic sorts that should be replaced.
     * @param instSorts
     *            the instantiations
     * @return returns a new term, where all generic variables are instantiated.
     *         If there is no generic variable the original term is returned.
     * @throws IllegalTacletException
     */
    private ImmutableList<Term> instantiateGeneric(Term term,
	    HashSet<GenericSort> genericSorts, ImmutableSet<Sort> instSorts,
	    Taclet t, TacletConditions conditions, int maxGeneric)
	    throws IllegalTacletException {
	ImmutableList<Term> instantiatedTerms = ImmutableSLList.nil();
	if (maxGeneric < genericSorts.size()) {
	    throw new IllegalTacletException(
		    "To many different generic sorts. Found: "
		            + genericSorts.size() + " Allowed: " + maxGeneric);

	}

	if (genericSorts.size() == 0) {

	    return null;
	}


	GenericSort genericTable[] = new GenericSort[genericSorts.size()];
	Sort instTable[] = new Sort[instSorts.size()];

	int i = 0;
	for (GenericSort sort : genericSorts) {
	    genericTable[i] = sort;
	    i++;
	}
	instTable = instSorts.toArray(instTable);

	byte[][] referenceTable = AbstractTacletTranslator.generateReferenceTable(instSorts.size(),
	        genericSorts.size());

	AbstractTacletTranslator.checkTable(referenceTable, instTable, genericTable, conditions);

	for (int r = 0; r < referenceTable.length; r++) {
	    Term temp = null;
	    for (int c = 0; c < referenceTable[r].length; c++) {
		int index = referenceTable[r][c];
		if (referenceTable[r][0] == -1)
		    break;
		if (!doInstantiation(genericTable[c], instTable[index],
		        conditions)) {
		    temp = null;
		    break;
		}

		try {
		    temp = instantiateGeneric(temp == null ? term : temp,
			    genericTable[c], instTable[index], t);
		    if (temp == null)
			break;
		} catch (TermCreationException e) {
		    for (TranslationListener l : listener) {
			if (l.eventInstantiationFailure(genericTable[c],
			        instTable[index], t, term))
			    throw e;
		    }
		    temp = null;
		    break;
		}

	    }
	    if (temp != null) {
		instantiatedTerms = instantiatedTerms.append(temp);
	    }

	}

	return instantiatedTerms;

    }

 



   

 

    public void addListener(TranslationListener listener) {
	this.listener.add(listener);
    }

    public void removeListener(TranslationListener listener) {
	this.listener.remove(listener);
    }

}
