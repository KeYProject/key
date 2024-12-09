/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.MutableState;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.Name;

/**
 * Projection of taclet apps to the instantiation of a schema variable. The projection can either be
 * partial and undefined for those apps that do not instantiate the schema variable in question, or
 * it can raise an error for such applications
 */
public class SVInstantiationProjection implements ProjectionToTerm {

    private final Name svName;
    private final boolean demandInst;

    private SVInstantiationProjection(Name svName, boolean demandInst) {
        this.svName = svName;
        this.demandInst = demandInst;
    }

    public static SVInstantiationProjection create(Name svName, boolean demandInst) {
        return new SVInstantiationProjection(svName, demandInst);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mutableState) {
        if (!(app instanceof final TacletApp tapp)) {
            Debug.fail("Projection is only applicable to taclet apps," + " but got " + app);
            throw new IllegalArgumentException(
                "Projections can only be applied to taclet applications, not to " + app);
        }
        final Object instObj = tapp.instantiations().lookupValue(svName);
        if (!(instObj instanceof Term instantiation)) {
            Debug.assertFalse(demandInst, "Did not find schema variable " + svName
                + " that I was supposed to examine" + " (taclet " + tapp.taclet().name() + ")");
            return null;
        }
        return instantiation;
    }


}
