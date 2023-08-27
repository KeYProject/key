/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;


import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;


class SortWrapper {
    private final Sort sort;
    private final StringBuilder name;
    private final StringBuilder predicateName;
    private final List<SortWrapper> parentSorts = new LinkedList<>();

    public boolean extendsTrans(SortWrapper sw) {
        return sw.getSort() != getSort() && getSort().extendsTrans(sw.getSort());
    }

    public Sort getSort() {
        return sort;
    }

    public StringBuilder getName() {
        return name;
    }

    public StringBuilder getPredicateName() {
        return predicateName;
    }

    public SortWrapper(Sort sort, StringBuilder name, StringBuilder predicateName) {
        super();
        this.sort = sort;
        this.name = name;
        this.predicateName = predicateName;
    }

    public List<SortWrapper> getParents() {
        return parentSorts;
    }

    void computeParentSorts(LinkedList<SortWrapper> sorts, boolean explicitNullHierarchy,
            boolean explicitHierarchy, Services services) {
        for (SortWrapper sw : sorts) {
            if (this.extendsTrans(sw)) {
                addParent(sw, explicitNullHierarchy, explicitHierarchy, services);
            }
        }
    }

    /**
     * Removes all sorts from parentSorts, that are not extended by this sort directly, i.e. the
     * sort <code>parent</code> is between <code>this.getSort()</code> and the considered sort.
     */
    private void removeGrandParents(SortWrapper parent) {
        parentSorts.removeIf(parent::extendsTrans);
    }

    private boolean addParent(SortWrapper parent, boolean explicitNullHierarchy,
            boolean explicitHierarchy, Services services) {
        Function nullOp = services.getTypeConverter().getHeapLDT().getNull();
        if ((explicitNullHierarchy && this.getSort() == nullOp.sort()) || explicitHierarchy) {
            parentSorts.add(parent);
            return true;
        }

        for (SortWrapper sw : parentSorts) {
            // only add the sort as parent, if it is a direct super sort.
            if (sw.extendsTrans(parent)) {
                return false;
            }
        }
        parentSorts.add(parent);

        removeGrandParents(parent);
        return true;

    }

}


/**
 * The SortHierarchy works as a wrapper class for sorts.
 *
 * @author Simon Greiner
 */
public class SortHierarchy {

    private final LinkedList<SortWrapper> sorts = new LinkedList<>();

    /**
     * Create a Sort Hierarchy.
     *
     * @param sortnames a HashMap of sorts mapped to the Strings which is displayed in Formulas
     */
    protected SortHierarchy(Map<Sort, StringBuilder> sortnames, Map<Sort, StringBuilder> prednames,
            boolean explicitNullHierarchy, boolean explicitHierarchy, Services services) {
        for (Entry<Sort, StringBuilder> entry : sortnames.entrySet()) {
            sorts.add(
                new SortWrapper(entry.getKey(), entry.getValue(), prednames.get(entry.getKey())));
        }

        for (SortWrapper sw : sorts) {
            sw.computeParentSorts(sorts, explicitNullHierarchy, explicitHierarchy, services);
        }

    }

    public List<SortWrapper> getSorts() {
        return sorts;
    }
}
