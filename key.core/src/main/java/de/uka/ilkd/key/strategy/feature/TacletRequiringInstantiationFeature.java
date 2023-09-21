/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.util.collection.ImmutableSet;

/**
 * Feature that returns zero iff the given rule app is a taclet app that needs explicit
 * instantiation of schema variables (which has not been done yet)
 */
public class TacletRequiringInstantiationFeature extends BinaryTacletAppFeature {

    public final static Feature INSTANCE = new TacletRequiringInstantiationFeature();

    private TacletRequiringInstantiationFeature() {
        super(false);
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        final ImmutableSet<SchemaVariable> neededVars = app.uninstantiatedVars();
        final ImmutableSet<SchemaVariable> ifFindVars = app.taclet().getIfFindVariables();
        for (SchemaVariable neededVar : neededVars) {
            if (!ifFindVars.contains(neededVar)) {
                return true;
            }
        }
        return false;
    }
}
