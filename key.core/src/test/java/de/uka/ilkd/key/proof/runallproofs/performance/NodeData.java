/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.performance;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

public class NodeData {

    final Map<String, RuleData> ruleName2RuleData = new HashMap<>();
    final int id;
    final int proofTreeDepth;
    final int astDepth;

    private static int getDepth(Node node) {
        int depth = -1;
        while (node != null) {
            node = node.parent();
            depth++;
        }
        return depth;
    }

    NodeData(Goal goal) {
        Node node = goal.node();
        id = node.serialNr();
        proofTreeDepth = getDepth(node);
        astDepth = countAST(node);
    }

    private static int countAST(Node n) {
        return countAST(n.sequent());
    }

    private static int countAST(Sequent sequent) {
        int sum = 0;
        for (SequentFormula f : sequent.antecedent().asList()) {
            sum += countAST(f.formula());
        }
        for (SequentFormula f : sequent.succedent().asList()) {
            sum += countAST(f.formula());
        }
        return sum;
    }

    private static int countAST(Term term) {
        int sum = 0;
        for (Term t : term.subs()) {
            sum += countAST(t);
        }
        return sum + 1;
    }

}
