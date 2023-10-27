/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

/**
 * This class contains the outsourced routines for KeY sort definitions and axioms for the modular
 * smtlib2 translation.
 *
 * Make sure that your master handler collects all relevent sorts (using
 * {@link MasterHandler#addSort(Sort)} during translation, and then call
 * {@link TypeManager#handle(MasterHandler)} to add the relevant declarations and axioms for the
 * type hierarchy to the handler.
 *
 * @author Jonas Schiffl
 * @author Mattias Ulbrich
 */
class TypeManager {

    private final Services services;

    TypeManager(Services services) {
        this.services = services;
    }

    /**
     * Creates a translated type hierarchy from the KeY sorts of the master handler by asserting the
     * subtype relationship (or its absence).
     *
     * @param master the master handler
     */
    private void createSortTypeHierarchy(MasterHandler master, Services services) {

        for (Sort s : master.getSorts()) {
            Set<Sort> children = directChildSorts(s, master.getSorts(), services);
            for (Sort child : children) {
                master.addAxiom(new SExpr("assert",
                    new SExpr("subtype", SExprs.sortExpr(child), SExprs.sortExpr(s))));
                for (Sort otherChild : children) {
                    if (!(child.equals(otherChild))
                            && (!otherChild.name().toString().equals("Null"))
                            && (!child.name().toString().equals("Null"))) {
                        SExpr st = new SExpr("subtype", SExprs.sortExpr(child),
                            SExprs.sortExpr(otherChild));
                        master.addAxiom(new SExpr("assert", new SExpr("not", st)));
                    }
                }
            }
        }

        // if sort has no direct parents, make it a child of any
        for (Sort s : master.getSorts()) {
            if (!(s instanceof NullSort) && !(s.equals(Sort.ANY))) {
                if (s.extendsSorts().isEmpty()) {
                    master.addAxiom(new SExpr("assert",
                        new SExpr("subtype", SExprs.sortExpr(s), SExprs.sortExpr(Sort.ANY))));
                }
            }
        }
    }

    /**
     * @param parent the (possible) parent sort
     * @param child the (possible) child sort
     * @return true iff parent is a direct parent sort of child
     */
    private boolean isDirectParentOf(Sort parent, Sort child, Services s) {
        return child.extendsSorts(s).contains(parent);
    }

    /**
     * @param s The parent sort
     * @param sorts the set of sorts to test
     * @return all direct child sorts of s in the set sorts
     */
    private Set<Sort> directChildSorts(Sort s, Set<Sort> sorts, Services services) {
        Set<Sort> res = new HashSet<>();
        for (Sort child : sorts) {
            if (isDirectParentOf(s, child, services)) {
                res.add(child);
            }
        }
        return res;
    }

    /**
     * make the constant declarations for the type constants. Each entry is of the form
     *
     * <pre>
     *     (declare-const sort_Name T)
     * </pre>
     *
     * Those symbols which are already known to the master handler are not created in the handler
     * but are still included in the result value.
     *
     * @param master the handler do which the declarations are added.
     * @return a freshly created list
     */
    private List<SExpr> makeSortDecls(MasterHandler master) {
        // turn all known sorts into sort constants ...
        List<SExpr> sortExprs = new LinkedList<>();
        for (Sort s : master.getSorts()) {
            SExpr sortExp = SExprs.sortExpr(s);
            if (!master.isKnownSymbol(sortExp.toString())) {
                master.addDeclaration(new SExpr("declare-const", sortExp, new SExpr("T")));
                master.addKnownSymbol(sortExp.toString());
            }
            sortExprs.add(SExprs.sortExpr(s));
        }
        return sortExprs;
    }

    /**
     * Add smt clauses related to KeY sorts to the provided handler.
     *
     * The sorts added to the handler are analysed, the respective constants are declared and axioms
     * regarding distinction and subtyping are added to master.
     *
     * @param master a master handler with collected sorts, will be modified
     */
    public void handle(MasterHandler master) {
        // declare the sort symbols ...
        List<SExpr> sortExprs = makeSortDecls(master);

        // ... which are mutually distinct
        if (master.getSorts().size() > 1) {
            master.addDeclaration(
                new SExpr("assert", Type.BOOL, new SExpr("distinct", Type.BOOL, sortExprs)));
        }

        // and have a type hierarchy.
        if (!HandlerUtil.PROPERTY_NO_TYPE_HIERARCHY.get(services)) {
            createSortTypeHierarchy(master, services);
        }
    }
}
