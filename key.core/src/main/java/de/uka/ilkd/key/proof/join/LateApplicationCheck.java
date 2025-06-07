/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.join;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.delayedcut.ApplicationCheck;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.NonNull;

/**
 * Methods for computing conflicts affecting a delayed cut application. Relies on the given
 * {@link ApplicationCheck} object.
 *
 * @see ApplicationCheck
 * @author Benjamin Niedermann
 */
public enum LateApplicationCheck {
    INSTANCE;

    public @NonNull List<String> check(@NonNull Node node, Node cutNode,
            @NonNull ApplicationCheck check) {
        return check(check, node.sequent(), cutNode);
    }

    private @NonNull List<String> check(@NonNull ApplicationCheck check, @NonNull Sequent sequent,
            Node cutNode) {
        List<String> conflicts = new LinkedList<>();
        for (SequentFormula sf : sequent) {
            String result = check.check(cutNode, (Term) sf.formula());
            if (result != null) {
                conflicts.add(result);
            }
        }
        return conflicts;
    }
}
