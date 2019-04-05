package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;

import java.util.HashSet;
import java.util.Set;

public class TypeManager {

    void createSortTypeHierarchy(MasterHandler master) {

        for (Sort s : master.getSorts()) {
            Set<Sort> children = directChildSorts(s, master.getSorts());
            for (Sort child : children) {
                master.addAxiom(new SExpr("assert", new SExpr("subtype", SExpr.sortExpr(child), SExpr.sortExpr(s))));
                for (Sort otherChild : children) {
                    if (!(child.equals(otherChild)) && (otherChild.name().toString() != ("Null")) && (child.name().toString() != ("Null"))) {
                        SExpr st = new SExpr("subtype", SExpr.sortExpr(child), SExpr.sortExpr(otherChild));
                        master.addAxiom(new SExpr("assert", new SExpr("not", st)));
                    }
                }
            }
        }
        // if sort has no direct parents, make it a child of any
        for (Sort s : master.getSorts()) {
            if (!(s instanceof NullSort) && !(s.equals(Sort.ANY))) {
                if (s.extendsSorts().isEmpty()) {
                    master.addAxiom(new SExpr("assert", new SExpr("subtype", SExpr.sortExpr(s), SExpr.sortExpr(Sort.ANY))));
                }
            }
        }
    }

    /*
     * @param parent the (possible) parent sort
     * @param child the (possible) child sort
     * @return true if parent is a direct parent sort of child
     */
    private boolean isDirectParentOf(Sort parent, Sort child) {
        if (!(child instanceof NullSort)) {
            return child.extendsSorts().contains(parent);
        } else {
            return true;
        }
    }

    private Set<Sort> directChildSorts(Sort s, Set<Sort> sorts) {
        Set<Sort> res = new HashSet<>();
        for (Sort child : sorts) {
            if (isDirectParentOf(s, child)) {
                res.add(child);
            }
        }
        return res;
    }
}
