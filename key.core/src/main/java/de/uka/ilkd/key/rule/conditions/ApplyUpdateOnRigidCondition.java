/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;


/**
 * This variable condition can be used to check whether an update can be performed on a formula.
 * That is the case if the
 * top-level operator is rigid and of arity greater than 0.
 *
 * @author Christoph Scheben
 * @author Tobias Reinhold
 */
public final class ApplyUpdateOnRigidCondition implements VariableCondition {

    /**
     * The schema variable matched against an update
     */
    private final UpdateSV u;

    /**
     * The schema variable matched against a formula
     */
    private final SchemaVariable phi;

    /**
     * The schema variable containing the result of applying the update <code>u</code> on the
     * formula <code>phi</code>
     */
    private final SchemaVariable result;

    /**
     * Creates an instance of the variable condition.
     *
     * @param u the schema variable matched against an update
     * @param phi the schema variable matched against a formula
     * @param result the schema variable containing the result of applying <code>u</code> on
     *        <code>phi</code>
     */
    public ApplyUpdateOnRigidCondition(UpdateSV u, SchemaVariable phi, SchemaVariable result) {
        this.u = u;
        this.phi = phi;
        this.result = result;
    }

    /**
     * <p>
     * Apply the update <code>u</code> on the rigid formula <code>phi</code>.
     * </p>
     * If any name clashes exist between the free variables in update <code>u</code> and the bound
     * variables in formula
     * <code>phi</code>, the names of those problematic bound variables will be changed.
     *
     * @param u the update applied on <code>phi</code>
     * @param phi the formula the update <code>u</code> is applied on
     * @param services the {@link Services} to help create terms
     * @return the term of the update <code>u</code> applied on all subterms of <code>phi</code> and
     *         possible renaming
     */
    private static Term applyUpdateOnRigid(Term u, Term phi, TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term[] updatedSubs = phi.subs().toArray(new Term[0]);

        final Set<Name> freeVarNamesInU = new HashSet<>();
        for (QuantifiableVariable freeVar : u.freeVars()) {
            freeVarNamesInU.add(freeVar.name());
        }

        final List<QuantifiableVariable> newBoundVarsInPhi = new ArrayList<>();
        final ImmutableArray<QuantifiableVariable> boundVarsInPhi = phi.boundVars();
        final int numOfBoundVars = boundVarsInPhi.size();
        for (int i = 0; i < numOfBoundVars; i++) {
            newBoundVarsInPhi.add(boundVarsInPhi.get(i));
        }

        // Check for any name clashes and change the variables' names if necessary
        for (int i = 0; i < numOfBoundVars; i++) {
            final QuantifiableVariable currentBoundVar = newBoundVarsInPhi.get(i);
            if (freeVarNamesInU.contains(currentBoundVar.name())) {
                final LogicVariable renamedVar =
                    new LogicVariable(createNonCollidingNameFor(currentBoundVar, u, phi),
                        currentBoundVar.sort());
                final Term substTerm = tb.var(renamedVar);

                final ClashFreeSubst subst = new ClashFreeSubst(currentBoundVar, substTerm, tb);
                for (int j = 0; j < updatedSubs.length; j++) {
                    updatedSubs[j] = subst.apply(updatedSubs[j]);
                }

                // rename quantifiable variable in set for later term construction
                newBoundVarsInPhi.set(i, renamedVar);
            }
        }

        // Apply update to all subterms
        for (int i = 0; i < updatedSubs.length; i++) {
            updatedSubs[i] = tb.apply(u, updatedSubs[i], null);
        }

        return services.getTermFactory().createTerm(phi.op(), updatedSubs,
            new ImmutableArray<>(newBoundVarsInPhi), phi.javaBlock());
    }

    /**
     * <p>
     * Creates a new non-colliding {@link Name} for <code>var</code>.
     * </p>
     * Currently, only the variables contained in <code>u</code> and <code>phi</code> are checked
     * for collisions. In the
     * future, it might be needed to check for collisions with variable names on higher levels.
     *
     * @param var the {@link QuantifiableVariable} to get a new {@link Name} for
     * @return a non-colliding {@link Name} for <code>var</code>
     */
    private static Name createNonCollidingNameFor(QuantifiableVariable var, Term u, Term phi) {
        ClashFreeSubst.VariableCollectVisitor vcv = new ClashFreeSubst.VariableCollectVisitor();
        ImmutableSet<QuantifiableVariable> usedVars = u.freeVars();
        phi.execPostOrder(vcv);
        usedVars = usedVars.union(vcv.vars());

        // Get a new name by adding a counter to the stem
        String stem = var.name().toString();
        int i = 1;
        while (nameIsAlreadyUsed(stem + i, usedVars)) {
            i++;
        }
        return new Name(stem + i);
    }

    /**
     * Checks whether a given <code>name</code> is already used by some {@link QuantifiableVariable}
     * in the set
     * <code>qvars</code>.
     *
     * @param name the name that is checked for occurrence in set <code>qvars</code>
     * @param qvars the set of {@link QuantifiableVariable}s to be checked for use of
     *        <code>name</code>
     * @return true iff <code>name</code> is already used in <code>qvars</code>
     */
    private static boolean nameIsAlreadyUsed(String name,
            ImmutableSet<QuantifiableVariable> qvars) {
        for (QuantifiableVariable qvar : qvars) {
            if (qvar.name().toString().equals(name)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        Term uInst = (Term) svInst.getInstantiation(u);
        Term phiInst = (Term) svInst.getInstantiation(phi);
        Term resultInst = (Term) svInst.getInstantiation(result);
        if (uInst == null || phiInst == null) {
            return mc;
        }

        if (!phiInst.op().isRigid() || phiInst.op().arity() == 0) {
            return null;
        }
        Term properResultInst = applyUpdateOnRigid(uInst, phiInst, services);
        if (resultInst == null) {
            svInst = svInst.add(result, properResultInst, services);
            return mc.setInstantiations(svInst);
        } else if (resultInst.equalsModRenaming(properResultInst)) {
            return mc;
        } else {
            return null;
        }
    }


    @Override
    public String toString() {
        return "\\applyUpdateOnRigid(" + u + ", " + phi + ", " + result + ")";
    }
}
