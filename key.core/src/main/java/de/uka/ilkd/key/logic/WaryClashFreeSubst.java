/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.WarySubstOp;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

public class WaryClashFreeSubst extends ClashFreeSubst {

    /** depth of recursion of the <code>apply</code> method */
    private int depth = 0;
    /** the formula should be prepended with a quantifier */
    private boolean createQuantifier = false;

    /**
     * variable with which the original variable should be substituted below modalities
     */
    private QuantifiableVariable newVar = null;
    private Term newVarTerm = null;

    /**
     * variables occurring within the original term and within the term to be substituted
     */
    private ImmutableSet<QuantifiableVariable> warysvars = null;

    public WaryClashFreeSubst(QuantifiableVariable v, Term s, TermBuilder tb) {
        super(v, s, tb);
        warysvars = null;
    }

    /**
     * substitute <code>s</code> for <code>v</code> in <code>t</code>, avoiding collisions by
     * replacing bound variables in <code>t</code> if necessary.
     */
    @Override
    public Term apply(Term t) {
        Term res;

        if (depth == 0) {
            if (!getSubstitutedTerm().isRigid()) {
                findUsedVariables(t);
            }
        }

        ++depth;
        try {
            res = super.apply(t);
        } finally {
            --depth;
        }

        if (createQuantifier && depth == 0) {
            res = addWarySubst(res);
        }

        return res;
    }

    /**
     * Determine a set of variables that do already appear within <code>t</code> or the substituted
     * term, and whose names should not be used for free variables
     */
    private void findUsedVariables(Term t) {
        VariableCollectVisitor vcv;

        vcv = new VariableCollectVisitor();
        getSubstitutedTerm().execPostOrder(vcv);
        warysvars = vcv.vars();

        vcv = new VariableCollectVisitor();
        t.execPostOrder(vcv);
        warysvars = warysvars.union(vcv.vars());
    }

    /**
     * Create a new logic variable to be used for substitutions below modalities
     */
    private void createVariable() {
        if (!createQuantifier) {
            createQuantifier = true;

            if (getSubstitutedTerm().freeVars().contains(getVariable())) {
                // in this case one might otherwise get collisions, as the
                // substitution might be carried out partially within the scope
                // of the original substitution operator
                newVar = newVarFor(getVariable(), warysvars);
            } else {
                newVar = getVariable();
            }
            newVarTerm = tb.var(newVar);
        }
    }

    /**
     * substitute <code>s</code> for <code>v</code> in <code>t</code>, avoiding collisions by
     * replacing bound variables in <code>t</code> if necessary. It is assumed, that <code>t</code>
     * contains a free occurrence of <code>v</code>.
     */
    @Override
    protected Term apply1(Term t) {
        // don't move to a different modality level
        if (!getSubstitutedTerm().isRigid()) {
            if (t.op() instanceof Modality) {
                return applyOnModality(t);
            }
            if (t.op() instanceof UpdateApplication) {
                return applyOnUpdate(t);
            }
        }
        if (t.op() instanceof Transformer) {
            return applyOnTransformer(t);
        }
        return super.apply1(t);
    }

    /**
     * Apply the substitution (that replaces a variable with a non-rigid term) on t, which has a
     * modality as top-level operator. This is done by creating a (top-level) existential
     * quantifier. This method is only called from <code>apply1</code> for substitutions with
     * non-rigid terms
     *
     * PRECONDITION: <code>warysvars != null</code>
     */
    private Term applyOnModality(Term t) {
        return applyBelowModality(t);
    }

    /**
     * Apply the substitution (that replaces a variable with a term) on t, which has a transformer
     * procedure as top-level operator. This is done by creating a (top-level) existential
     * quantifier. This method is only called from <code>apply1</code> for substitutions with
     * non-rigid terms
     *
     * PRECONDITION: <code>warysvars != null</code>
     */
    private Term applyOnTransformer(Term t) {
        return applyBelowTransformer(t);
    }

    /**
     * Apply the substitution (that replaces a variable with a non-rigid term) on t, which has an
     * update operator as top-level operator. This is done by creating a (top-level) existential
     * quantifier. This method is only called from <code>apply1</code> for substitutions with
     * non-rigid terms
     *
     * PRECONDITION: <code>warysvars != null</code>
     */
    private Term applyOnUpdate(Term t) {

        // only the last child is below the update
        final Term target = UpdateApplication.getTarget(t);
        if (!target.freeVars().contains(getVariable())) {
            return super.apply1(t);
        }

        final Term[] newSubterms = new Term[t.arity()];
        @SuppressWarnings("unchecked")
        final ImmutableArray<QuantifiableVariable>[] newBoundVars = new ImmutableArray[t.arity()];

        final int targetPos = UpdateApplication.targetPos();
        for (int i = 0; i < t.arity(); i++) {
            if (i != targetPos) {
                applyOnSubterm(t, i, newSubterms, newBoundVars);
            }
        }

        newBoundVars[targetPos] = t.varsBoundHere(targetPos);
        final boolean addSubst = subTermChanges(t.varsBoundHere(targetPos), target);
        newSubterms[targetPos] = addSubst ? substWithNewVar(target) : target;

        return tb.tf().createTerm(t.op(), newSubterms, getSingleArray(newBoundVars), t.javaBlock());
    }

    /**
     * Apply the substitution to a term/formula below a modality or update
     */
    private Term applyBelowModality(Term t) {
        return substWithNewVar(t);
    }

    /**
     * Apply the substitution to a term/formula below a transformer procedure
     */
    private Term applyBelowTransformer(Term t) {
        return substWithNewVar(t);
    }

    /**
     * Prepend the given term with a wary substitution (substituting <code>newVar</code> with
     * <code>getSubstitutedTerm()</code>)
     */
    private Term addWarySubst(Term t) {
        createVariable();
        return tb.subst(WarySubstOp.SUBST, newVar, getSubstitutedTerm(), t);
    }

    /**
     * Rename the original variable to be substituted to <code>newVar</code>
     */
    private Term substWithNewVar(Term t) {
        createVariable();
        final ClashFreeSubst cfs = new ClashFreeSubst(getVariable(), newVarTerm, tb);
        return cfs.apply(t);
    }
}
