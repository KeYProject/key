/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;

public class TermCollector implements DefaultVisitor {

    private final Set<Term> terms = new HashSet<>();

    @Override
    public void visit(Term visited) {
        terms.add(visited);
    }

    public Set<Term> getTerms() {
        return terms;
    }

}
