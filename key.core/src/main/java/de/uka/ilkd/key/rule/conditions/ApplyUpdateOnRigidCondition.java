/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableArray;


public final class ApplyUpdateOnRigidCondition implements VariableCondition {

    private final UpdateSV u;
    private final SchemaVariable phi;
    private final SchemaVariable result;

    public ApplyUpdateOnRigidCondition(UpdateSV u, SchemaVariable phi, SchemaVariable result) {
        this.u = u;
        this.phi = phi;
        this.result = result;
    }

    // 1. u.freeVars() -> alle freien vars im Update
    // 2. Namen der freien vars suchen
    // 3. phi Term fragen, welche vars gebunden werden: phi.boundVars()
    // 4. Schnitt von 2 und 3: Substitution: {u}{old_x/new_x}phi.sub(i)
    // 4.1. Position beibehalten
    // 4.2. new LogicVariable
    // 4.3. services.getTermBuilder().subst(old_x, services.getTermBuilder().var(new_x),
    // phi.sub(i));
    private static Term applyUpdateOnRigid(Term u, Term phi, TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term[] updatedSubs = phi.subs().toArray(new Term[0]);

        final Set<Name> freeVarNamesInU = new HashSet<>();
        for (QuantifiableVariable freeVar : u.freeVars()) {
            freeVarNamesInU.add(freeVar.name());
        }

        final ImmutableArray<QuantifiableVariable> boundVarsInPhi = phi.boundVars();
        final int numOfBoundVars = boundVarsInPhi.size();
        final List<QuantifiableVariable> newBoundVarsInPhi = new ArrayList<>();
        for (int i = 0; i < numOfBoundVars; i++) {
            newBoundVarsInPhi.add(boundVarsInPhi.get(i));
        }

        // Check for any name clashes and change the variables' names if necessary.
        for (int i = 0; i < numOfBoundVars; i++) {
            final QuantifiableVariable currentBoundVar = newBoundVarsInPhi.get(i);
            if (freeVarNamesInU.contains(currentBoundVar.name())) {
                // find new way to name variable
                LogicVariable renamedVar =
                    new LogicVariable(new Name(tb.newName(currentBoundVar.name().toString())),
                        currentBoundVar.sort());
                Term substTerm = tb.var(renamedVar);

                for (int j = 0; j < updatedSubs.length; j++) {
                    updatedSubs[j] =
                        WarySubstOp.SUBST.apply(
                            tb.subst(WarySubstOp.SUBST, currentBoundVar, substTerm, updatedSubs[j]),
                            tb);
                }

                newBoundVarsInPhi.set(i, renamedVar);
            }
        }

        // Apply update to all subterms.
        for (int i = 0; i < updatedSubs.length; i++) {
            updatedSubs[i] = tb.apply(u, updatedSubs[i], null);
        }

        return services.getTermFactory().createTerm(phi.op(), updatedSubs,
            new ImmutableArray<>(newBoundVarsInPhi), phi.javaBlock());
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
