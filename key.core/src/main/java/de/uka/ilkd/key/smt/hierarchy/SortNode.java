/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.hierarchy;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Represents a node in the class hierarchy. Each SortNode contains a Sort and links to SortNodes
 * containing the parents and the children of the sort.
 *
 * @author mihai
 */
public class SortNode {
    private final Sort sort;

    private final Set<SortNode> parents;
    private final Set<SortNode> children;

    public SortNode(Sort sort) {
        this.sort = sort;
        parents = new HashSet<>();
        children = new HashSet<>();
    }

    public void removeParent(SortNode s) {
        parents.remove(s);
    }

    public void addParent(SortNode s) {
        parents.add(s);
    }

    public void removeChild(SortNode s) {
        children.remove(s);
    }

    public void addChild(SortNode s) {
        children.add(s);
    }


    public Sort getSort() {
        return sort;
    }


    public Set<SortNode> getParents() {
        return parents;
    }


    public Set<SortNode> getChildren() {
        return children;
    }

    @Override
    public String toString() {
        return sort.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(sort.toString());
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o instanceof SortNode) {
            Sort s = ((SortNode) o).getSort();
            return s.toString().equals(sort.toString());
        }
        return false;
    }
}
