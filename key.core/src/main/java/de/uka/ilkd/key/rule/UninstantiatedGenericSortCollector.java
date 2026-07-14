/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NonNull;

public class UninstantiatedGenericSortCollector extends TacletSchemaVariableCollector {
    /** collects all found variables */
    protected @NonNull Set<GenericSort> sortList = new HashSet<>();

    /**
     * @param svInsts the SVInstantiations that have been already found (needed by unwind loop
     *        constructs to determine which labels are needed)
     */
    public UninstantiatedGenericSortCollector(@NonNull SVInstantiations svInsts) {
        super(svInsts);
    }

    @Override
    public void visit(@NonNull Term p_visited) {
        visit(p_visited.sort());
        for (var t : p_visited.subs()) {
            visit(t);
        }
        for (var bv : p_visited.boundVars()) {
            visit(bv.sort());
        }
    }

    private void visit(Sort s) {
        if (s instanceof GenericSort gs
                && !instantiations.getGenericSortInstantiations().isInstantiated(gs)) {
            sortList.add(gs);
        } else if (s instanceof ParametricSortInstance psi) {
            for (var a : psi.getArgs()) {
                visit(a.sort());
            }
        }
    }

    public Set<GenericSort> getSortList() {
        return sortList;
    }
}
