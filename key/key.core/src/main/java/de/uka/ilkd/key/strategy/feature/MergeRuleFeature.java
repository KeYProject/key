// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * Costs for the {@link MergeRule}; cheap if the first statement in the chosen
 * top-level formula is a {@link MergePointStatement}, otherwise, infinitely
 * expensive.
 *
 * @author Dominic Scheurer
 */
public class MergeRuleFeature implements Feature {
    public static final Feature INSTANCE = new MergeRuleFeature();

    private MergeRuleFeature() {
        // Singleton constructor
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos,
            Goal goal) {
        final Term t = pos.subTerm();
        if (!pos.isTopLevel() || !t.containsJavaBlockRecursive()) {
            return TopRuleAppCost.INSTANCE;
        }

        return JavaTools.getActiveStatement(TermBuilder.goBelowUpdates(t)
                .javaBlock()) instanceof MergePointStatement
                        ? NumberRuleAppCost.create(0)
                        : TopRuleAppCost.INSTANCE;
    }

}
