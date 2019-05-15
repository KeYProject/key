package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

class TypeManager {

    /** A set of sorts that require special treatment in the type hierarchy,
     * e.g., the null sort or the int and bool sorts that also exist in smtlib.
     */
    private static final Set<String> SPECIAL_SORTS =
            Stream.of("int", "boolean", "Null").collect(Collectors.toSet());

    /**
     * Creates a translated type hierarchy from the KeY sorts of the master handler
     * by asserting the subtype relationship (or its absence).
     * @param master the master handler
     */
    void createSortTypeHierarchy(MasterHandler master) {

        for (Sort s : master.getSorts()) {
            Set<Sort> children = directChildSorts(s, master.getSorts());
            for (Sort child : children) {
                if (!isSpecialSort(s)) {
                    master.addAxiom(new SExpr("assert", new SExpr("subtype", SExpr.sortExpr(child), SExpr.sortExpr(s))));
                }
                for (Sort otherChild : children) {
                    if (!(child.equals(otherChild)) && (!otherChild.name().toString().equals("Null"))
                            && (!child.name().toString().equals("Null"))) {
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

    /**
     * @param parent the (possible) parent sort
     * @param child the (possible) child sort
     * @return true iff parent is a direct parent sort of child
     */
    private boolean isDirectParentOf(Sort parent, Sort child) {
        if (!(child instanceof NullSort)) {
            return child.extendsSorts().contains(parent);
        } else {
            return true;
        }
    }

    /**
     * @param s The parent sort
     * @param sorts the set of sorts to test
     * @return all direct child sorts of s in the set sorts
     */
    private Set<Sort> directChildSorts(Sort s, Set<Sort> sorts) {
        Set<Sort> res = new HashSet<>();
        for (Sort child : sorts) {
            if (isDirectParentOf(s, child)) {
                res.add(child);
            }
        }
        return res;
    }

    static boolean isSpecialSort(Sort sort) {
        return SPECIAL_SORTS.contains(sort.toString());
    }
}
