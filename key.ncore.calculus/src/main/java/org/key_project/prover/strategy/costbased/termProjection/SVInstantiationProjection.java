/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termProjection;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

/// Projection of taclet apps to the instantiation of a schema variable. The projection can either
/// be
/// partial and undefined for those apps that do not instantiate the schema variable in question, or
/// it can raise an error for such applications
public class SVInstantiationProjection<G extends ProofGoal<G>> implements ProjectionToTerm<G> {

    private final Name svName;
    private final boolean demandInst;

    private SVInstantiationProjection(Name svName, boolean demandInst) {
        this.svName = svName;
        this.demandInst = demandInst;
    }

    public static <G extends ProofGoal<G>> SVInstantiationProjection<G> create(Name svName,
            boolean demandInst) {
        return new SVInstantiationProjection<>(svName, demandInst);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, G goal, MutableState mutableState) {
        if (!(app instanceof final ITacletApp tapp)) {
            throw new IllegalArgumentException(
                "Projections can only be applied to taclet applications, not to " + app);
        }
        final Object instObj = tapp.instantiations().lookupValue(svName);
        if (!(instObj instanceof Term instantiation)) {
            assert !demandInst;
            return null;
        }
        return instantiation;
    }


}
