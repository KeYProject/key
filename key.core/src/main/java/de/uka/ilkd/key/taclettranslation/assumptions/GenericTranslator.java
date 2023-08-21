/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.assumptions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

class GenericTranslator {
    private final VariablePool pool;
    private final ArrayList<TranslationListener> listener = new ArrayList<>();
    private Services services;

    GenericTranslator(VariablePool pool) {
        this.pool = pool;
    }

    /**
     * Translates generic variables.
     */
    public Collection<Term> translate(Term term, ImmutableSet<Sort> sorts, Taclet t,
            TacletConditions conditions, Services serv, int maxGeneric)
            throws IllegalTacletException {
        this.services = serv;

        Set<GenericSort> generics = AssumptionGenerator.collectGenerics(term);
        ImmutableList<Term> list =
            instantiateGeneric(term, generics, sorts, t, conditions, maxGeneric);
        Collection<Term> result = new LinkedList<>();
        if (list == null) {
            result.add(term);
            return result;
        }

        if (list.isEmpty()) {
            throw new IllegalTacletException("Can not instantiate generic variables"
                + " because there are not enough different sorts. " + generics + " " + sorts);
        }

        if (list.size() > 0) {
            for (Term gt : list) {
                result.add(AssumptionGenerator.quantifyTerm(gt, services));

            }
        }

        return result;
    }

    private boolean sameHierachyBranch(Sort sort1, Sort sort2) {

        return sort1.extendsTrans(sort2) || sort2.extendsTrans(sort1);
    }

    /**
     * Instantiates all variables of a generic sort with logic variables. The logic variable has the
     * same name with the prefix [sort]__
     *
     * @param term
     * @param generic the generic sort that should be instantiated.
     * @param instantiation the instantiation sort.
     * @return returns the new term with instantiated variables. If <code>term</code> can not be
     *         instantiated the method returns <code>null</code>, e.g. this can occur, when
     *         <code>term</code> is of type {@link SortDependingFunction} and
     *         <code>instantiation</code> is of type {PrimitiveSort}.
     */

    private Term instantiateGeneric(Term term, GenericSort generic, Sort instantiation, Taclet t)
            throws IllegalArgumentException, IllegalTacletException {
        Term[] subTerms = new Term[term.arity()];
        ImmutableArray<QuantifiableVariable> variables = term.boundVars();
        for (int i = 0; i < term.arity(); i++) {
            subTerms[i] = instantiateGeneric(term.sub(i), generic, instantiation, t);

            if (subTerms[i] == null) {
                return null;
            }

        }

        if (term.sort().equals(generic)) {

            if (term.op() instanceof LogicVariable) {
                TermBuilder tb = services.getTermBuilder();
                term = tb.var(
                    pool.getInstantiationOfLogicVar(instantiation, (LogicVariable) term.op()));
            } else if (term.op() instanceof SchemaVariable) {
                if (term.op() instanceof TermSV) {
                    final var logicVariable = pool.getLogicVariable(term.op().name(), term.sort());
                    final var instantiationOfLogicVar =
                        pool.getInstantiationOfLogicVar(instantiation, logicVariable);
                    term = services.getTermBuilder().var(instantiationOfLogicVar);
                }

            }

        }

        if (term.op() instanceof SortDependingFunction) {

            SortDependingFunction func = (SortDependingFunction) term.op();
            try { // Try block is necessary because there are some
                  // taclets
                  // that should have isReference-Condition, but
                  // they don't
                  // have the condition.

                if (func.getSortDependingOn().equals(generic)) {
                    if (instantiation.extendsTrans(services.getJavaInfo().nullSort())) {
                        return null;
                    }
                    func = func.getInstanceFor(instantiation, services);

                    if (func.getKind().equals(Sort.CAST_NAME)) {
                        for (int i = 0; i < term.arity(); i++) {

                            if (!sameHierachyBranch(func.getSortDependingOn(),
                                subTerms[i].sort())) {
                                // don't
                                // instantiate
                                // casts, that
                                // don't make
                                // sense.
                                return null;
                            }
                        }
                    }

                    term = services.getTermFactory().createTerm(func, subTerms);

                }
            } catch (IllegalArgumentException e) {
                for (TranslationListener l : listener) {
                    if (l.eventInstantiationFailure(generic, instantiation, t, term)) {
                        throw e;
                    }
                }
                return null;
            }
        }

        if (term.op() instanceof Quantifier) {

            QuantifiableVariable[] copy = new QuantifiableVariable[term.boundVars().size()];
            assert copy.length == 1;
            int i = 0;

            for (QuantifiableVariable var : term.boundVars()) {
                copy[i] = var;
                if (copy[i].sort() instanceof GenericSort) {

                    copy[i] = pool.getInstantiationOfLogicVar(instantiation,
                        pool.getLogicVariable(copy[i].name(), instantiation));
                }

                i++;
            }
            if ((term.op()).equals(Quantifier.ALL)) {
                term = services.getTermBuilder().all(copy[0], subTerms[0]);
            }
            if ((term.op()).equals(Quantifier.EX)) {
                term = services.getTermBuilder().ex(copy[0], subTerms[0]);
            }

        } else {

            term = services.getTermFactory().createTerm(term.op(), subTerms, variables,
                JavaBlock.EMPTY_JAVABLOCK);

        }

        return term;

    }

    /**
     * Tests sort of its instantiation ability.
     *
     * @return <code>true</code> if <code>generic</code> can be instantiated with <code>inst</code>,
     *         otherwise <code>false</code>
     */
    private boolean doInstantiation(GenericSort generic, Sort inst, TacletConditions conditions) {

        return !((inst instanceof GenericSort) || (inst.equals(Sort.ANY))
                || (conditions.containsIsReferenceCondition(generic) > 0
                        && !AssumptionGenerator.isReferenceSort(inst, services))
                || (conditions.containsNotAbstractInterfaceCondition(generic)
                        && AssumptionGenerator.isAbstractOrInterface(inst, services))
                || (conditions.containsAbstractInterfaceCondition(generic)
                        && !AssumptionGenerator.isAbstractOrInterface(inst, services)));
    }

    /**
     * Instantiates generic variables of the term. It instantiates the variables using all
     * possibilities.
     *
     * @param term the term to be instantiated.
     * @param genericSorts the generic sorts that should be replaced.
     * @param instSorts the instantiations
     * @return returns a new term, where all generic variables are instantiated. If there is no
     *         generic variable the original term is returned.
     * @throws IllegalTacletException
     */
    private ImmutableList<Term> instantiateGeneric(Term term, Set<GenericSort> genericSorts,
            ImmutableSet<Sort> instSorts, Taclet t, TacletConditions conditions, int maxGeneric)
            throws IllegalTacletException {
        ImmutableList<Term> instantiatedTerms = ImmutableSLList.nil();
        if (maxGeneric < genericSorts.size()) {
            throw new IllegalTacletException("To many different generic sorts. Found: "
                + genericSorts.size() + " Allowed: " + maxGeneric);

        }

        if (genericSorts.isEmpty()) {
            return null;
        }

        GenericSort[] genericTable = new GenericSort[genericSorts.size()];
        Sort[] instTable = new Sort[instSorts.size()];

        int i = 0;
        for (GenericSort sort : genericSorts) {
            genericTable[i] = sort;
            i++;
        }
        instTable = instSorts.toArray(instTable);

        byte[][] referenceTable =
            AssumptionGenerator.generateReferenceTable(instSorts.size(), genericSorts.size());

        AssumptionGenerator.checkTable(referenceTable, instTable, genericTable, conditions,
            services);

        for (byte[] bytes : referenceTable) {
            Term temp = null;
            for (int c = 0; c < bytes.length; c++) {
                int index = bytes[c];

                if (bytes[0] == -1) {
                    break;
                }

                if (!doInstantiation(genericTable[c], instTable[index], conditions)) {
                    temp = null;
                    break;
                }

                try {
                    temp = instantiateGeneric(temp == null ? term : temp, genericTable[c],
                        instTable[index], t);
                    if (temp == null) {
                        break;
                    }
                } catch (TermCreationException e) {
                    for (TranslationListener l : listener) {
                        if (l.eventInstantiationFailure(genericTable[c], instTable[index], t,
                            term)) {
                            throw e;
                        }
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

    public void addListener(TranslationListener list) {
        this.listener.add(list);
    }

    public void removeListener(TranslationListener list) {
        this.listener.remove(list);
    }

}
