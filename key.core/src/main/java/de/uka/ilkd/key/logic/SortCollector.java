/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.logic.DefaultVisitor;

/**
 * @author mihai
 *
 */
public class SortCollector extends DefaultVisitor<Sort> {
    /** the collected sorts */
    private final Set<Sort> sorts = new HashSet<>();

    public Set<Sort> getSorts() {
        return sorts;
    }

    /*
     * (non-Javadoc)
     *
     * @see org.key_project.logic.DefaultVisitor#visit(de.uka.ilkd.key.logic.Term)
     */
    @Override
    public void visit(org.key_project.logic.Term<Sort> visited) {
        sorts.add(visited.sort());
    }

}
