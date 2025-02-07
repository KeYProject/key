/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.LinkedList;
import java.util.Queue;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (06.02.25)
 */
public class TermUtil {

    /**
     * Checks if a given term contains a specific operator.
     *
     * This method performs a breadth-first search on the term's subterms to find
     * the specified operator.
     *
     * Caveat: It does not return true if op (only) occurs as the target of an update in term.
     *
     * @param term the term to be checked
     * @param op the operator to search for
     * @return true if the term or any of its subterms contains the operator, false otherwise
     */
    public static boolean contains(@NonNull Term term, @NonNull Operator op) {
        Queue<Term> queue = new LinkedList<>();
        queue.add(term);
        while (!queue.isEmpty()) {
            Term current = queue.poll();
            if (current.op() == op) {
                return true;
            }
            queue.addAll(current.subs().toList());
        }
        return false;
    }
}
