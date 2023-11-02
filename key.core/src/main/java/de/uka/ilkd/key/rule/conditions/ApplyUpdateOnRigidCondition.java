/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


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
        Term[] updatedSubs = new Term[phi.arity()];
        for (int i = 0; i < updatedSubs.length; i++) {
            updatedSubs[i] = services.getTermBuilder().apply(u, phi.sub(i), null);
        }
        Term result = services.getTermFactory().createTerm(phi.op(), updatedSubs,
            phi.boundVars(), phi.javaBlock());
        return result;
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
        } else if (resultInst.equals(properResultInst)) {
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
