/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.logic;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @author mihai
 *
 */
public class SortCollector extends DefaultVisitor {

    private Set<Sort> sorts;

    public SortCollector() {
        sorts = new HashSet<Sort>();
    }

    public Set<Sort> getSorts() {
        return sorts;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.logic.DefaultVisitor#visit(de.uka.ilkd.key.logic.Term)
     */
    @Override
    public void visit(Term visited) {
        sorts.add(visited.sort());
    }

}
