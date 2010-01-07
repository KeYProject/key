// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;

import java.util.ArrayList;
import java.util.HashSet;

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
    public Term translate(Term term, ImmutableSet<Sort> sorts, Taclet t,
	    TacletConditions conditions, Services services, int maxGeneric)
	    throws IllegalTacletException {
	this.services = services;
	ImmutableList<Term> list = instantiateGeneric(term,
	        collectGenerics(term), sorts, t, conditions, maxGeneric);

	if (list == null)
	    return term;

	if (list.isEmpty()) {
	    throw new IllegalTacletException(
		    "Can not instantiate generic variables"
		            + " because there are not enough different sorts.");
	}

	// quantify the term
	ImmutableList<Term> genericTermsQuantified = ImmutableSLList.nil();
	if (list.size() > 0) {
	    for (Term gt : list) {
		genericTermsQuantified = genericTermsQuantified
		        .append(AbstractTacletTranslator.quantifyTerm(gt));

	    }
	    if (appendGenericTerm) {
		genericTermsQuantified = genericTermsQuantified.append(term);
	    }
	    term = TermBuilder.DF.and(genericTermsQuantified);

	}

	return term;

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

	}/*
	  * else if(AbstractTacletTranslator.isCreatedTerm(term, services)&&
	  * !(term.sub(0).sort() instanceof GenericSort) ){ term=
	  * AbstractTacletTranslator.createCreatedTerm(term.sub(0), services);
	  * }else if(AbstractTacletTranslator.isNextToCreateTerm(term) &&
	  * !(term.sub(0).sort() instanceof GenericSort) ){
	  * if(!(term.sub(0).sort() instanceof ObjectSort)){
	  * 
	  * }
	  * 
	  * term.sub(0).sort(); term =
	  * AbstractTacletTranslator.createNextToCreateTerm
	  * ((ObjectSort)term.sub(0).sort(), services); }
	  */else {
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
     * using all possibilities. This method supports two different generic
     * variables and the following variable conditions: - \not\same(G,H)
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
    // old version - only for comparing results
    private Term instantiateGeneric(Term term,
	    HashSet<GenericSort> genericSorts, ImmutableSet<Sort> instSorts,
	    Taclet t, TacletConditions conditions)
	    throws IllegalTacletException {
	if (genericSorts.size() == 0) {
	    return term;
	}
	if (genericSorts.size() > 2) {
	    throw new IllegalTacletException("Can not translate taclets with "
		    + "more than two generic sorts.");
	}

	ImmutableList<Term> genericTerms = ImmutableSLList.nil();

	GenericSort gs[] = new GenericSort[2];
	int i = 0;
	for (GenericSort sort : genericSorts) {
	    gs[i] = sort;
	    i++;
	}

	// instantiate the first generic variable
	for (Sort sort1 : instSorts) {

	    if (!doInstantiation(gs[0], sort1, conditions)) {
		continue;
	    }

	    Term temp = null;
	    try {
		temp = instantiateGeneric(term, gs[0], sort1, t);
	    } catch (TermCreationException e) {
		for (TranslationListener l : listener) {
		    if (l.eventInstantiationFailure(gs[0], sort1, t, term))
			throw e;
		}
	    }

	    if (temp == null) {
		continue;
	    }

	    // instantiate the second generic variable
	    if (genericSorts.size() == 2) {
		int instCount = 0;
		for (Sort sort2 : instSorts) {
		    if (!(conditions.containsNotSameCondition(gs[0], gs[1]) && sort1
			    .equals(sort2))
			    && doInstantiation(gs[1], sort2, conditions)) {
			Term temp2 = null;
			try {
			    temp2 = instantiateGeneric(temp, gs[1], sort2, t);
			} catch (TermCreationException e) {
			    for (TranslationListener l : listener) {
				if (l.eventInstantiationFailure(gs[1], sort2,
				        t, term))
				    throw e;
			    }
			}

			if (temp2 != null) {
			    instCount++;
			    genericTerms = genericTerms.append(temp2);
			}

		    }

		}
		if (instCount == 0) {
		    throw new IllegalTacletException(
			    "Can not instantiate generic variables"
			            + " because there are not enough different sorts.");
		}

	    } else {
		genericTerms = genericTerms.append(temp);
	    }

	}

	if (genericTerms.size() == 0) {
	    throw new IllegalTacletException(
		    "Can not instantiate generic variables"
		            + " because there are not enough different sorts.");
	}

	// quantify the term
	ImmutableList<Term> genericTermsQuantified = ImmutableSLList.nil();
	if (genericTerms.size() > 0) {
	    for (Term gt : genericTerms) {
		genericTermsQuantified = genericTermsQuantified
		        .append(AbstractTacletTranslator.quantifyTerm(gt));

	    }
	    if (appendGenericTerm) {
		genericTermsQuantified = genericTermsQuantified.append(term);
	    }
	    term = TermBuilder.DF.and(genericTermsQuantified);

	}

	return term;
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
		    "To many different generic sorts. Founded: "
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

	byte[][] referenceTable = generateReferenceTable(instSorts.size(),
	        genericSorts.size());

	check(referenceTable, instTable, genericTable, conditions);

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

    /**
     * Checks the referenceTable whether there are rows that are not allowed.
     * For example: the notSame-Condition is hurted.
     * 
     * @param referenceTable
     * @param r
     * @param instTable
     * @param genericTable
     */
    private void check(byte[][] referenceTable, Sort[] instTable,
	    GenericSort[] genericTable, TacletConditions conditions) {

	for (int r = 0; r < referenceTable.length; r++) {
	    for (int c = 0; c < referenceTable[r].length; c++) {
		int index = referenceTable[r][c];
		if (referenceTable[r][0] == -1)
		    break;

		if ((conditions.containsIsReferenceCondition(genericTable[c]) > 0 && !AbstractTacletTranslator
		        .isReferenceSort(instTable[index]))
		        || (conditions
		                .containsAbstractInterfaceCondition(genericTable[c]) && !AbstractTacletTranslator
		                .isAbstractOrInterface(instTable[index]))
		        || (conditions
		                .containsNotAbstractInterfaceCondition(genericTable[c]) && AbstractTacletTranslator
		                .isAbstractOrInterface(instTable[index])))

		{
		    referenceTable[r][0] = -1;
		    break;

		}
		for (int c2 = c + 1; c2 < referenceTable[r].length; c2++) {
		    int index2 = referenceTable[r][c2]; // not same
		    if ((conditions.containsNotSameCondition(genericTable[c],
			    genericTable[c2]) && instTable[index]
			    .equals(instTable[index2]))
			    || // 
			    (genericTable[c].extendsTrans(genericTable[c2]) && !instTable[index]
			            .extendsTrans(instTable[index2]))

		    ) {
			referenceTable[r][0] = -1;
			break;
		    }

		}

	    }
	}

    }

    private byte[][] generateReferenceTable(int instSize, int genSize) {

	int colCount = genSize;
	int rowCount = (int) Math.pow(instSize, genSize);
	byte max = (byte) ((byte) instSize - 1);

	byte table[][] = new byte[rowCount][colCount];

	for (int r = 1; r < rowCount; r++) {
	    int temp = 1;
	    for (int c = 0; c < colCount; c++) {
		byte newVal = (byte) (table[r - 1][c] + temp);
		if (newVal > max) {
		    newVal = 0;
		    temp = 1;
		} else {
		    temp = 0;
		}
		table[r][c] = newVal;

	    }

	}

	return table;
    }

    private HashSet<GenericSort> collectGenerics(Term term) {
	HashSet<GenericSort> genericSorts = new HashSet<GenericSort>();
	collectGenerics(term, genericSorts);
	return genericSorts;
    }

    private void collectGenerics(Term term, HashSet<GenericSort> genericSorts) {

	if (term.op() instanceof SortDependingFunction) {
	    SortDependingFunction func = (SortDependingFunction) term.op();
	    if (func.getSortDependingOn() instanceof GenericSort) {
		genericSorts.add((GenericSort) func.getSortDependingOn());
	    }
	}

	if (term.sort() instanceof GenericSort) {
	    genericSorts.add((GenericSort) term.sort());
	}
	for (int i = 0; i < term.arity(); i++) {
	    collectGenerics(term.sub(i), genericSorts);
	}

    }

    public void addListener(TranslationListener listener) {
	this.listener.add(listener);
    }

    public void removeListener(TranslationListener listener) {
	this.listener.remove(listener);
    }

}
