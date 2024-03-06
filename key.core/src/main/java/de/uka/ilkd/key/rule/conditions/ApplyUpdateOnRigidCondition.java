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

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.logic.equality.RenamingProperty.RENAMING_PROPERTY;


/**
 * This variable condition can be used to check whether an update can be performed on a formula or
 * term.
 * That is the case if the top-level operator is rigid and of arity greater than 0.
 *
 * @author Benjamin Weiss
 * @author Tobias Reinhold
 */
public final class ApplyUpdateOnRigidCondition implements VariableCondition {

    /**
     * The schema variable matched against an update
     */
    private final UpdateSV u;

    /**
     * The schema variable matched against a formula or term
     */
    private final SchemaVariable phi;

    /**
     * The schema variable containing the result of applying the update <code>u</code> on the
     * formula or term <code>phi</code>
     */
    private final SchemaVariable result;

    /**
     * Creates an instance of the variable condition.
     *
     * @param u the schema variable matched against an update
     * @param phi the schema variable matched against a formula or term
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
     * Applies the update <code>u</code> on the rigid formula or term <code>phi</code>.
     * </p>
     * If there are free variables in <code>u</code>,
     * {@link #applyUpdateOnRigidClashAware(Term, Term, TermServices)} is
     * called to take care of potential name clashes.
     *
     * @param u the update applied on <code>phi</code>
     * @param phi the formula or term the update <code>u</code> is applied on
     * @param services the {@link TermServices} to help create terms
     * @return the term of the update <code>u</code> applied on all subterms of <code>phi</code> and
     *         possible renaming
     */
    private static Term applyUpdateOnRigid(Term u, Term phi, TermServices services) {
        // If there are no free variables in u, we don't have to check for name collisions
        if (u.freeVars().isEmpty()) {
            final TermBuilder tb = services.getTermBuilder();
            final Term[] updatedSubs = new Term[phi.arity()];
            for (int i = 0; i < updatedSubs.length; i++) {
                updatedSubs[i] = tb.apply(u, phi.sub(i));
            }

            return services.getTermFactory().createTerm(phi.op(), updatedSubs, phi.boundVars(),
                null);
        }

        // Here we have to check for name collisions as there are free variables in u
        return applyUpdateOnRigidClashAware(u, phi, services);
    }

    /**
     * <p>
     * This method is used by {@link #applyUpdateOnRigid(Term, Term, TermServices)} if there are
     * free variables in <code>u</code>.
     * </p>
     * If any name clashes exist between the free variables in <code>u</code> and the bound
     * variables in
     * <code>phi</code>, the names of those problematic bound variables will be changed.
     *
     * @param u the update applied on <code>phi</code>
     * @param phi the formula or term the update <code>u</code> is applied on
     * @param services the {@link TermServices} to help create terms
     * @return the term of the update <code>u</code> applied on all subterms of <code>phi</code> and
     *         possible renaming
     */
    private static Term applyUpdateOnRigidClashAware(Term u, Term phi, TermServices services) {
        final TermBuilder tb = services.getTermBuilder();

        final Set<Name> freeVarNamesInU = new HashSet<>();
        for (QuantifiableVariable freeVar : u.freeVars()) {
            freeVarNamesInU.add(freeVar.name());
        }

        final QuantifiableVariable[] boundVarsInPhi =
            phi.boundVars().toArray(new QuantifiableVariable[0]);

        final Term[] updatedSubs = phi.subs().toArray(new Term[0]);
        // Check for any name clashes and change the variables' names if necessary
        for (int i = 0; i < boundVarsInPhi.length; i++) {
            final QuantifiableVariable currentBoundVar = boundVarsInPhi[i];
            if (freeVarNamesInU.contains(currentBoundVar.name())) {
                final LogicVariable renamedVar =
                    new LogicVariable(createNonCollidingNameFor(currentBoundVar, u, phi, services),
                        currentBoundVar.sort());
                final Term substTerm = tb.var(renamedVar);

                final ClashFreeSubst subst = new ClashFreeSubst(currentBoundVar, substTerm, tb);
                for (int j = 0; j < updatedSubs.length; j++) {
                    updatedSubs[j] = subst.apply(updatedSubs[j]);
                }

                // Rename quantifiable variable in list for later term construction
                boundVarsInPhi[i] = renamedVar;
            }
        }

        for (int i = 0; i < updatedSubs.length; i++) {
            updatedSubs[i] = tb.apply(u, updatedSubs[i]);
        }

        return services.getTermFactory().createTerm(phi.op(), updatedSubs,
            new ImmutableArray<>(boundVarsInPhi), null);
    }

    /**
     * <p>
     * Creates a new non-colliding {@link Name} for <code>var</code>.
     * </p>
     * Currently, only the variables contained in <code>u</code> and <code>phi</code> are checked
     * for collisions. In the future, it might be needed to check for collisions with variable names
     * on higher levels.
     *
     * @param var the {@link QuantifiableVariable} to get a new {@link Name} for
     * @param u the update that is checked for variables
     * @param phi the formula or term that is checked for variables
     * @param services the {@link TermServices} to help create terms
     * @return a non-colliding {@link Name} for <code>var</code>
     */
    private static Name createNonCollidingNameFor(QuantifiableVariable var, Term u, Term phi,
            TermServices services) {
        ClashFreeSubst.VariableCollectVisitor vcv = new ClashFreeSubst.VariableCollectVisitor();
        ImmutableSet<QuantifiableVariable> usedVars = u.freeVars();
        phi.execPostOrder(vcv);
        usedVars = usedVars.union(vcv.vars());

        // Get a new name by adding a counter to the stem
        String stem = var.name().toString();
        int i = 1;
        Name newName;
        do {
            newName = new Name(stem + i);
            i++;
        } while (nameIsAlreadyUsed(newName, usedVars, services));
        return newName;
    }

    /**
     * Checks whether the given <code>name</code> is already used by some
     * {@link QuantifiableVariable} in the set
     * <code>qvars</code> or the {@link NamespaceSet}.
     *
     * @param name the {@link Name} that is checked for occurrence in set <code>qvars</code>
     * @param qvars the set of {@link QuantifiableVariable}s to be checked for use of
     *        <code>name</code>
     * @param services the {@link TermServices} to help create terms
     * @return true iff <code>name</code> is already used in <code>qvars</code>
     */
    private static boolean nameIsAlreadyUsed(Name name, ImmutableSet<QuantifiableVariable> qvars,
            TermServices services) {
        for (QuantifiableVariable qvar : qvars) {
            if (qvar.name().equals(name)) {
                return true;
            }
        }
        return services.getNamespaces().lookupLogicSymbol(name) != null;
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
        } else if (resultInst.equalsModProperty(properResultInst, RENAMING_PROPERTY)) {
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
