/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;


/**
 * Some generally useful tools for dealing with arrays of bound variables
 */
public class BoundVariableTools {

    public final static BoundVariableTools DEFAULT = new BoundVariableTools();

    private BoundVariableTools() {}

    /**
     * Compare the arrays <code>oldBoundVars</code> and <code>newBoundVars</code> component-wise,
     * and in case of differences substitute variables from the former array with the ones of the
     * latter array (in <code>originalTerm</code>)
     *
     * @param services the Services
     */
    public JTerm renameVariables(JTerm originalTerm,
            ImmutableArray<QuantifiableVariable> oldBoundVars,
            ImmutableArray<QuantifiableVariable> newBoundVars, TermServices services) {
        JTerm res = originalTerm;
        for (int i = 0; i != oldBoundVars.size(); ++i) {
            if (oldBoundVars.get(i) != newBoundVars.get(i)) {
                final JTerm newVarTerm = services.getTermFactory().createTerm(newBoundVars.get(i));
                final ClashFreeSubst subst =
                    new ClashFreeSubst(oldBoundVars.get(i), newVarTerm, services.getTermBuilder());
                res = subst.apply(res);
            }
        }

        return res;
    }

    public JTerm[] renameVariables(JTerm[] originalTerms,
            ImmutableArray<QuantifiableVariable> oldBoundVars,
            ImmutableArray<QuantifiableVariable> newBoundVars, TermServices services) {
        final JTerm[] res = new JTerm[originalTerms.length];
        for (int i = 0; i != res.length; ++i) {
            res[i] = renameVariables(originalTerms[i], oldBoundVars, newBoundVars, services);
        }
        return res;
    }


    /**
     * Replace all variables of <code>oldVars</code> that also turn up in <code>criticalPairs</code>
     * with new variables (currently just with the same name).
     *
     * @param oldVars variables to be checked
     * @param newVars array in which either the original variables (if a variable is not an element
     *        of <code>criticalVars</code>) or newly created variables are stored
     * @param criticalVars variables that must not turn up in the resulting array
     *        <code>newVars</code>
     * @return <code>true</code> iff it was necessary to create at least one new variable
     */
    public boolean resolveCollisions(ImmutableArray<QuantifiableVariable> oldVars,
            QuantifiableVariable[] newVars, ImmutableSet<QuantifiableVariable> criticalVars) {
        boolean changedVar = false;

        for (int i = 0; i != newVars.length; ++i) {
            final QuantifiableVariable oldVar = oldVars.get(i);
            if (criticalVars.contains(oldVar)) {
                // rename the bound variable
                newVars[i] = new LogicVariable(oldVar.name(), oldVar.sort());
                changedVar = true;
            } else {
                newVars[i] = oldVar;
            }
        }

        return changedVar;
    }

    /**
     * Ensure that none of the variables <code>criticalVars</code> is bound by the top-level
     * operator of <code>t</code> (by bound renaming)
     */
    // public Term resolveCollisions (Term t,
    // ImmutableSet<QuantifiableVariable> criticalVars) {
    // final ImmutableArray<QuantifiableVariable>[] newBoundVars =
    // new ImmutableArray<QuantifiableVariable> [t.arity ()];
    // final Term[] newSubs = new Term [t.arity ()];
    //
    // if ( !resolveCollisions ( t, criticalVars, newBoundVars, newSubs ) )
    // return t;
    //
    // return tf.createTerm ( t.op (), newSubs, newBoundVars, t.javaBlock ());
    // }

    /**
     * Ensure that none of the variables <code>criticalVars</code> is bound by the top-level
     * operator of <code>t</code> (by bound renaming). The resulting subterms and arrays of bound
     * variables are stored in <code>newSubs</code> and <code>newBoundVars</code> (resp.)
     *
     * @param services TODO
     *
     * @return <code>true</code> if it was necessary to rename a variable, i.e. to changed anything
     *         in the term <code>originalTerm</code>
     */
    public boolean resolveCollisions(JTerm originalTerm,
            ImmutableSet<QuantifiableVariable> criticalVars,
            ImmutableArray<QuantifiableVariable>[] newBoundVars, JTerm[] newSubs,
            TermServices services) {
        boolean changed = false;

        for (int i = 0; i != originalTerm.arity(); ++i) {
            final ImmutableArray<QuantifiableVariable> oldVars = originalTerm.varsBoundHere(i);

            final QuantifiableVariable[] newVars = new QuantifiableVariable[oldVars.size()];
            if (resolveCollisions(oldVars, newVars, criticalVars)) {
                changed = true;
                newBoundVars[i] = new ImmutableArray<>(newVars);
                newSubs[i] =
                    renameVariables(originalTerm.sub(i), oldVars, newBoundVars[i], services);
            } else {
                newBoundVars[i] = oldVars;
                newSubs[i] = originalTerm.sub(i);
            }
        }

        return changed;
    }


    /**
     * Ensure that for the subterms with indexes [<code>subtermsBegin</code>,
     * <code>subtermsEnd</code>) the same variables are bound. In case of differences bound renaming
     * is applied (existing variables are renamed to new ones)
     *
     * @param boundVarsPerSub bound variables per subterms
     * @param subs subterms (in which variables are renamed if necessary)
     * @param subtermsBegin first subterm that is supposed to be considered
     * @param subtermsEnd subterm after the last subterm to be consider
     *
     *        PRE: <code>subtermsEnd {@literal >} subtermsBegin</code>
     * @param services TODO
     */
    public ImmutableArray<QuantifiableVariable> unifyBoundVariables(
            ImmutableArray<QuantifiableVariable>[] boundVarsPerSub, JTerm[] subs,
            int subtermsBegin,
            int subtermsEnd, TermServices services) {
        // at least one subterms belongs to the entry (value)
        ImmutableArray<QuantifiableVariable> unifiedVariable = boundVarsPerSub[subtermsBegin];

        final Map<QuantifiableVariable, QuantifiableVariable> variableRenamings =
            new LinkedHashMap<>();
        for (int i = subtermsBegin + 1; i < subtermsEnd; ++i) {
            // check that numbers and sorts of the quantified variables are
            // consistent
            Debug.assertTrue(consistentVariableArrays(unifiedVariable, boundVarsPerSub[i]),
                "Inconsistent bound variables");

            unifiedVariable =
                unifyVariableArrays(unifiedVariable, boundVarsPerSub[i], variableRenamings);
        }

        // substitute variables where necessary
        for (int i = subtermsBegin; i < subtermsEnd; ++i) {
            subs[i] = renameVariables(subs[i], boundVarsPerSub[i], unifiedVariable, services);
        }

        return unifiedVariable;
    }

    /**
     * @return <code>true</code> iff the two given arrays have the same size and the contained
     *         variables have the same sorts
     */
    public boolean consistentVariableArrays(ImmutableArray<QuantifiableVariable> ar0,
            ImmutableArray<QuantifiableVariable> ar1) {
        if (ar0.size() != ar1.size()) {
            return false;
        }
        for (int i = 0; i != ar0.size(); ++i) {
            if (ar0.get(i).sort() != ar1.get(i).sort()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @param services TODO
     * @return <code>true</code> iff the two arrays of variables are compatible
     *         (<code>compatibleVariableArrays()</code>) and the two given terms are equal modulo
     *         renaming after unification of the two arrays (of variables occurring free in the
     *         terms)
     */
    public boolean equalsModRenaming(ImmutableArray<QuantifiableVariable> vars0, JTerm term0,
            ImmutableArray<QuantifiableVariable> vars1, JTerm term1, TermServices services) {
        if (!consistentVariableArrays(vars0, vars1)) {
            return false;
        }
        if (vars0.size() == 0) {
            return RENAMING_TERM_PROPERTY.equalsModThisProperty(term0, term1);
        }

        final ImmutableArray<QuantifiableVariable> unifiedVars = unifyVariableArrays(vars0, vars1,
            new LinkedHashMap<>());

        final JTerm renamedTerm0 = renameVariables(term0, vars0, unifiedVars, services);
        final JTerm renamedTerm1 = renameVariables(term1, vars1, unifiedVars, services);

        return RENAMING_TERM_PROPERTY.equalsModThisProperty(renamedTerm0, renamedTerm1);
    }

    /**
     * Unify the given arrays be replacing variables with new ones, return the unifier
     */
    private ImmutableArray<QuantifiableVariable> unifyVariableArrays(
            ImmutableArray<QuantifiableVariable> ar0, ImmutableArray<QuantifiableVariable> ar1,
            Map<QuantifiableVariable, QuantifiableVariable> variableRenaming) {
        final QuantifiableVariable[] res = new QuantifiableVariable[ar0.size()];
        for (int i = 0; i != ar0.size(); ++i) {
            QuantifiableVariable pv0 = ar0.get(i);
            if (variableRenaming.containsKey(pv0)) {
                pv0 = variableRenaming.get(pv0);
            }

            QuantifiableVariable pv1 = ar1.get(i);
            if (variableRenaming.containsKey(pv1)) {
                pv1 = variableRenaming.get(pv1);
            }

            if (pv0 != pv1) {
                // introduce a new variable
                final QuantifiableVariable newVar = new LogicVariable(pv0.name(), pv0.sort());
                variableRenaming.put(ar0.get(i), newVar);
                variableRenaming.put(ar1.get(i), newVar);
                variableRenaming.put(pv0, newVar);
                variableRenaming.put(pv1, newVar);
                res[i] = newVar;
            } else {
                res[i] = pv0;
            }
        }

        return new ImmutableArray<>(res);
    }
}
