/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.BinaryTacletAppFeature;

import org.key_project.logic.Name;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public class IntroducedSymbolBy extends BinaryTacletAppFeature {
    private final Name ruleSetName;
    private final Name schemaVar;
    private final ProjectionToTerm<Goal> term;

    public static Feature create(ProjectionToTerm<Goal> termWithTopLevelOpToCheck,
            String ruleSetName,
            String schemaVar) {
        return new IntroducedSymbolBy(termWithTopLevelOpToCheck, new Name(ruleSetName),
            new Name(schemaVar));
    }

    protected IntroducedSymbolBy(ProjectionToTerm<Goal> termWithTopLevelOpToCheck, Name ruleSetName,
            Name schemaVar) {
        this.term = termWithTopLevelOpToCheck;
        this.ruleSetName = ruleSetName;
        this.schemaVar = schemaVar;
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Node root = goal.proof().root();

        Node n = goal.node();
        while (n != root) {
            final RuleApp ra = n.getAppliedRuleApp();
            if (ra instanceof TacletApp ta) {
                if (ta.taclet().getRuleSets().contains(new RuleSet(ruleSetName))) {
                    final Object svInstValue = ta.instantiations().lookupValue(schemaVar);
                    if (svInstValue instanceof JTerm svInstAsTerm) {
                        return term.toTerm(app, pos, goal, mState).op() == svInstAsTerm.op();
                    }
                }
            }
            n = n.parent();
        }
        return false;
    }
}
