/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.LinkedList;
import java.util.Queue;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * @author Alexander Weigl
 * @version 1 (06.02.25)
 */
public class TermUtil {
    public static boolean contains(Term term, Operator forbiddenHeapVar) {
        Queue<Term> queue = new LinkedList<>();
        queue.add(term);
        while (!queue.isEmpty()) {
            Term current = queue.poll();
            if (current.op() == forbiddenHeapVar) {
                return true;
            }
            queue.addAll(current.subs().toList());
        }
        return false;
    }
}
