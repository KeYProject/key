/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.hierarchy;

import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.sort.Sort;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Represents the hierarchy of the Java reference types known to KeY.
 *
 * @author mihai
 */

public class TypeHierarchy {
    private static final Logger LOGGER = LoggerFactory.getLogger(TypeHierarchy.class);

    /**
     * Maps each sort to its SortNode. The SortNode contains the parents and children of the sort.
     */
    private final HashMap<Sort, SortNode> sortMap = new HashMap<>();
    /**
     * List of known java reference sorts.
     */
    private final List<Sort> sortList = new LinkedList<>();
    /**
     * List of known array sorts.
     */
    private final List<Sort> arraySortList = new LinkedList<>();
    /**
     * The KeY services.
     */
    private final Services services;

    public TypeHierarchy(Services services) {
        this.services = services;

        // Find all sorts
        for (var sort : services.getNamespaces().sorts().allElements()) {
            // don't add the null sort
            if (!sort.equals(services.getTypeConverter().getHeapLDT().getNull().sort())) {
                addSort(sort);
                sortList.add(sort);

                if (sort.name().toString().endsWith("[]")) {
                    arraySortList.add(sort);
                }
            }
        }

        // For all found sorts find their parents and children.
        for (Entry<Sort, SortNode> e : sortMap.entrySet()) {
            Sort s = e.getKey();
            SortNode n = e.getValue();

            for (Sort p : s.extendsSorts(services)) {
                // get parent node
                SortNode pn = sortMap.get(p);
                if (pn == null) {
                    continue;
                }
                n.addParent(pn);
                pn.addChild(n);
            }
        }
    }

    /**
     * @return The list of sorts in the type hierarchy.
     */
    public List<Sort> getSortList() {
        return sortList;
    }

    /**
     * @return The list of array sorts in the type hierarchy.
     */
    public List<Sort> getArraySortList() {
        return arraySortList;
    }

    private void addSort(Sort s) {
        SortNode node = new SortNode(s);
        sortMap.put(s, node);
    }

    /**
     * Returns the children of a sort s.
     *
     * @param s A sort s.
     * @return The SortNodes containing the children of s.
     */
    public Set<SortNode> getChildren(Sort s) {

        if (sortMap.get(s) == null) {
            return new HashSet<>();
        }
        return sortMap.get(s).getChildren();
    }

    /**
     * Returns the parents of a sort s.
     *
     * @param s A sort s.
     * @return The SortNodes containing the parents of s.
     */
    public Set<SortNode> getParents(Sort s) {
        return sortMap.get(s).getParents();
    }

    /**
     * Removes all interface sorts from the type hierarchy. All sorts without non-interface parents
     * become children of java.lang.Object. All other sorts are left unchanged.
     */
    public void removeInterfaceNodes() {

        JavaInfo info = services.getJavaInfo();

        // find all interface sorts and contract them
        Set<Sort> interfaceSorts = new HashSet<>();
        for (Sort s : sortMap.keySet()) {

            KeYJavaType kjt = info.getKeYJavaType(s);
            if (kjt != null) {
                Type jt = kjt.getJavaType();
                if (jt instanceof InterfaceDeclaration) {
                    // contract interface sort
                    contractNode(s);
                    interfaceSorts.add(s);
                }
            }


        }
        // remove the found interface sorts from the map
        for (Sort sort : interfaceSorts) {
            sortMap.remove(sort);
        }
        /*
         * Some sorts may end up with two parents, one of which is java.lang.Object. In those cases
         * we remove java.lang.Object as parent.
         */
        for (var e : sortMap.entrySet()) {
            var node = e.getValue();
            if (node.getParents().size() > 1) {
                Set<SortNode> toRemove = new HashSet<>();
                for (SortNode p : node.getParents()) {
                    if (p.getSort().toString().equals("java.lang.Object")) {
                        p.removeChild(node);
                        toRemove.add(p);
                    }
                }
                for (SortNode p : toRemove) {
                    node.removeParent(p);
                }

            }
        }


    }

    /**
     * Contracts a sort s. Removes s as child of its parents and parent of its children. The
     * children of s become the children of all parents of s and vice-versa.
     *
     * @param s The sort to be contracted.
     */
    private void contractNode(Sort s) {
        SortNode node = sortMap.get(s);
        Set<SortNode> parents = node.getParents();
        Set<SortNode> children = node.getChildren();


        // add children as children of parent
        for (SortNode p : parents) {
            p.removeChild(node);
            for (SortNode c : children) {
                p.addChild(c);
            }
        }
        // add parents as parents of children
        for (SortNode c : children) {
            c.removeParent(node);
            for (SortNode p : parents) {
                c.addParent(p);
            }
        }
    }


    public void print() {
        for (Entry<Sort, SortNode> e : sortMap.entrySet()) {
            Sort s = e.getKey();
            SortNode n = e.getValue();

            String sorttype = s.isAbstract() ? "abstract" : "concrete";
            LOGGER.debug("{} {}", sorttype, s);
            LOGGER.debug("Parents: {}", n.getParents());
            LOGGER.debug("Children:{} ", n.getChildren());

        }
    }

}
