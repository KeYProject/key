package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static de.uka.ilkd.key.smt.newsmt2.SExpr.*;

class TypeManager {

    /** A set of sorts that require special treatment in the type hierarchy,
     * e.g. int and bool sorts that also exist in smtlib.
     */
    private static final Set<String> EMBEDDED_SORTS =
        Stream.of("int", "boolean").collect(Collectors.toSet());
    private static final String NULL_SORT = "Null";

    /** The services for looking up direct parent sorts of NullSort. */
    private final Services services;

    public TypeManager(Services services) {
        this.services = services;
    }

    /**
     * Creates a translated type hierarchy from the KeY sorts of the master handler
     * by asserting a case distinction over all subtypes.
     * @param master the master handler
     */
    void createSortTypeHierarchy(MasterHandler master) {
        // axioms common for special as well as object sorts
        createSortDefAxioms(master);

        /* The hierarchy has two parts with different axioms: top level (any + direct subtypes),
         * and everything below the java.lang.Object sort. The latter has to be handled specifically
         * because of the Null sort (which actually destroys the antisymmetry and thus the partial
         * order property of the subtype relation). */
        createTopLevelHierarchyAxiom(master);
        createObjectTypeHierarchy(master);
    }

    private void createSortDefAxioms(MasterHandler master) {
        Set<Sort> allSorts = master.getSorts();
        for (Sort s : allSorts) {
            Set<Sort> directChildren = directChildSorts(s, allSorts);
            master.addAxiom(new SExpr("assert", sortDefAxiom(s, directChildren)));
        }
    }

    private SExpr sortDefAxiom(Sort s, Set<Sort> directChildren) {
        SExpr sortS = SExprs.sortExpr(s);
        SExpr u = new SExpr("u");
        SExpr exactS = new SExpr("exactinstanceof", Type.BOOL, u, sortS);
        SExpr instS = new SExpr("instanceof", Type.BOOL, u, sortS);

        // since interfaces are not subtype of any class, they can not occur here!
        List<SExpr> literals = new ArrayList<>();
        literals.add(exactS);
        for (Sort child : directChildren) {
            SExpr sortChild = SExprs.sortExpr(child);
            SExpr instChild = new SExpr("instanceof", Type.BOOL, u, sortChild);
            literals.add(instChild);
        }
        SExpr or = SExprs.or(literals.toArray(new SExpr[0]));

        // TODO: this could be to weak; maybe we need <-> here (but this is not modularly sound!)
        SExpr imp = SExprs.imp(or, instS);
        SExpr bindU = new SExpr("u", Type.NONE, "U");
        return new SExpr("forall", new SExpr(bindU), imp);
    }

    // axiom for Any and direct subtypes
    private void createTopLevelHierarchyAxiom(MasterHandler master) {
        Set<Sort> allSorts = master.getSorts();

        Sort anySort = services.getNamespaces().sorts().lookup("any");
        assert anySort != null;     // assumption: any sort is always present!

        // amo: exactInst(any), inst(int), inst(bool), ...
        Set<Sort> anyChildren = directChildSorts(anySort, allSorts);
        SExpr bindU = new SExpr("u", Type.NONE, "U");
        SExpr amoSort = amoTopLevelSort(anySort, anyChildren);
        master.addAxiom(new SExpr("assert", new SExpr("forall", new SExpr(bindU), amoSort)));
    }

    // do not use with object sorts!
    private SExpr amoTopLevelSort(Sort parent, Set<Sort> directChildren) {
        SExpr u = new SExpr("u");

        List<SExpr> andParams = new ArrayList<>();
        List<Sort> sortList = new ArrayList<>(directChildren);
        for (int i = 0; i < sortList.size(); i++) {
            SExpr si = SExprs.sortExpr(sortList.get(i));
            SExpr notInstSi = new SExpr("not", new SExpr("instanceof", u, si));
            for (int j = i + 1; j < sortList.size(); j++) {
                SExpr sj = SExprs.sortExpr(sortList.get(j));
                SExpr notInstSj = new SExpr("not", new SExpr("instanceof", u, sj));
                SExpr or = SExprs.or(notInstSi, notInstSj);
                andParams.add(or);
            }
            // also disjoint to exactinstance of parent
            SExpr sortParent = SExprs.sortExpr(parent);
            SExpr exactInstParent = new SExpr("exactinstanceof", u, sortParent);
            SExpr or = SExprs.or(notInstSi, new SExpr("not", exactInstParent));
            andParams.add(or);
        }
        return SExprs.and(andParams);
    }

    private boolean isInterfaceSort(Sort s) {
        KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(s);
        assert kjt != null;
        return services.getJavaInfo().isInterface(kjt);
    }

    // axioms for object types
    private void createObjectTypeHierarchy(MasterHandler master) {
        Set<Sort> allSorts = master.getSorts();
        // for every sort subsort of Object (st_i are all _direct_ subtypes):
        // instanceof(x, s) <- exactinstanceof(x, s) | instanceof(x, st_1)
        //                                           | instanceof(x, st_2)
        //                                           | ...
        //                                           | instanceof(x, st_n)
        Sort objectSort = services.getJavaInfo().objectSort();
        Set<Sort> objectSorts = allSorts.stream()
                                        .filter(s -> s.extendsTrans(objectSort))
                                        .filter(s -> !isInterfaceSort(s))
                                        .collect(Collectors.toSet());
        objectSorts.add(objectSort);

        // if x is instance of two direct child sorts it must be null
        Sort nullSort = services.getJavaInfo().nullSort();
        for (Sort os : objectSorts) {
            List<Sort> directChildren = new ArrayList<>(directChildSorts(os, allSorts));
            directChildren.remove(nullSort);

            /*
            // Since implementing multiple interfaces is allowed, we have to remove them here!
            Iterator<Sort> childIterator = directChildren.iterator();
            while (childIterator.hasNext()) {
                Sort c = childIterator.next();
                KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(c);
                if (services.getJavaInfo().isInterface(kjt)) {
                    childIterator.remove();
                }
            }*/

            // for each childSort c:
            // at most one of instanceof(c) or exactinstanceof(parent)
            SExpr u = new SExpr("u");
            for (Sort c : directChildren) {
                SExpr amoParentChild = atMostOneObjectSort(os, c);
                master.addAxiom(new SExpr("assert", amoParentChild));
            }

            if (directChildren.isEmpty() || directChildren.size() == 1) {
                continue;   // else we would get: (forall ((u U)) (= u null))
            }
            Set<SExpr> pairs = new HashSet<>();
            // for every pair of subtypes (!= Null):
            for (int i = 0; i < directChildren.size(); i++) {
                Sort sortI = directChildren.get(i);
                SExpr instSortI = new SExpr("instanceof", Type.BOOL, u, SExprs.sortExpr(sortI));
                for (int j = i + 1; j < directChildren.size(); j++) {
                    Sort sortJ = directChildren.get(j);
                    SExpr instSortJ = new SExpr("instanceof", Type.BOOL, u, SExprs.sortExpr(sortJ));
                    SExpr and = SExprs.and(instSortI, instSortJ);
                    pairs.add(and);
                }
            }
            // TODO: using hardcoded symbol k_null is a bad idea if null translation changes
            SExpr uEqNull = new SExpr("=", Type.BOOL, "u", "k_null");
            SExpr imp = SExprs.imp(SExprs.or(pairs.toArray(new SExpr[0])), uEqNull);
            SExpr bindU = new SExpr("u", Type.NONE, "U");
            SExpr all = new SExpr("forall", new SExpr(bindU), imp);
            master.addAxiom(new SExpr("assert", all));
        }
    }

    // for object sorts!
    // at most one of: instanceof(child), exactinstanceof(parent)
    private static SExpr atMostOneObjectSort(Sort parent, Sort child) {
        SExpr sortParent = SExprs.sortExpr(parent);
        SExpr sortChild = SExprs.sortExpr(child);
        SExpr u = new SExpr("u");
        SExpr instSortC = new SExpr("instanceof", Type.BOOL, u, sortChild);
        SExpr exInstParent = new SExpr("exactinstanceof", Type.BOOL, u, sortParent);
        SExpr or = SExprs.or(new SExpr("not", exInstParent), new SExpr("not", instSortC));
        SExpr bindU = new SExpr("u", Type.NONE, "U");
        return new SExpr("forall", new SExpr(bindU), or);
    }

    void createSortTypeHierarchyTest(MasterHandler master) {
        // IMPORTANT: this translation is modularly unsound!
        // assumption: closed type hierarchy: all types are known at translation type
        for (Sort s : master.getSorts()) {
            Set<Sort> subTypes = collectAllSubtypes(s, master.getSorts());
            // forall u U; instanceof(x, s) <-> (exactinstanceof(x, s)
            //                                 | instanceof(x, subt0)
            //                                 | instanceof(x, subt1)
            //                                 | ... )
            SExpr u = new SExpr("u");
            SExpr lhs = SExprs.instanceOf(u, SExprs.sortExpr(s));
            SExpr rhs = new SExpr("exactinstanceof", u, SExprs.sortExpr(s));
            List<SExpr> ors = new ArrayList<>();
            ors.add(rhs);
            for (Sort st : subTypes) {
                ors.add(SExprs.instanceOf(u, SExprs.sortExpr(st)));
            }
            rhs = SExprs.or(ors.toArray(new SExpr[0]));
            SExpr matrix = new SExpr("=", lhs, rhs);
            SExpr bindU = new SExpr("u", Type.NONE, "U");
            SExpr all = new SExpr("forall", Type.BOOL, new SExpr(bindU), matrix);
            master.addAxiom(new SExpr("assert", all));
        }
    }

    public void rollOutCastAxioms(MasterHandler master) {
        for (Sort s : master.getSorts()) {  // TODO: some special sorts could probably be excluded
            // two axioms to add
            // (assert (forall ((u U)) (instanceof (cast u s) s)))
            SExpr sort = SExprs.sortExpr(s);
            SExpr u = new SExpr("u");
            SExpr cast = new SExpr("cast", Type.UNIVERSE, u, sort);
            SExpr inst = SExprs.instanceOf(cast, sort);
            SExpr bindU = new SExpr("u", Type.NONE, "U");
            SExpr axiom0 = new SExpr("forall", new SExpr(bindU), inst);
            master.addAxiom(new SExpr("assert", axiom0));

            // (assert (forall ((u U)) (=> (instanceof u s) (= (cast u s) u))))
            SExpr inst2 = SExprs.instanceOf(u, sort);
            SExpr eq = new SExpr("=", cast, u);
            SExpr imp = new SExpr("=>", inst2, eq);
            SExpr axiom1 = new SExpr("forall", new SExpr(bindU), imp);
            master.addAxiom(new SExpr("assert", axiom1));
        }
    }

    public void rollOutTypeguardAxioms(MasterHandler master) {
        for (Sort s : master.getSorts()) {  // TODO: some special sorts could probably be excluded
            // (assert (forall ((u U)) (= (typeguard u s) (instanceof u s))))
            SExpr sort = SExprs.sortExpr(s);
            SExpr u = new SExpr("u");
            SExpr typeguard = new SExpr("typeguard", Type.BOOL, u, sort);
            SExpr inst = SExprs.instanceOf(u, sort);
            SExpr eq = new SExpr("=", typeguard, inst);
            SExpr bindU = new SExpr("u", Type.NONE, "U");
            SExpr axiom = new SExpr("forall", new SExpr(bindU), eq);
            master.addAxiom(new SExpr("assert", axiom));
        }
    }

    // IMPORTANT: not modularly sound, since it makes a case distinction about all (known) sorts
    private void amoTypeAxiom(MasterHandler master) {
        SExpr u = new SExpr("u");

        // each variable has at most one exact type
        List<SExpr> andParams = new ArrayList<>();
        List<Sort> sortList = new ArrayList<>(master.getSorts());
        for (int i = 0; i < sortList.size(); i++) {
            SExpr si = SExprs.sortExpr(sortList.get(i));
            SExpr notExactInstSi = new SExpr("not", new SExpr("exactinstanceof", u, si));
            for (int j = i + 1; j < sortList.size(); j++) {
                SExpr sj = SExprs.sortExpr(sortList.get(j));
                SExpr notExactInstSj = new SExpr("not", new SExpr("exactinstanceof", u, sj));
                SExpr or = SExprs.or(notExactInstSi, notExactInstSj);
                andParams.add(or);
            }
        }
        SExpr amoType = SExprs.and(andParams);
        SExpr bindU = new SExpr("u", Type.NONE, "U");
        SExpr axiom = new SExpr("forall", new SExpr(bindU), amoType);
        master.addAxiom(new SExpr("assert", axiom));
    }

    /**
     * Creates a translated type hierarchy from the KeY sorts of the master handler
     * by asserting the subtype relationship (or its absence).
     * @param master the master handler
     */
    void createSortTypeHierarchyOld(MasterHandler master) {
        // IMPORTANT: the original type hierarchy translation with subtype and typeof leads to
        //  Z3 proofs that are not replayable (since these symbols have not direct KeY counterpart)
        for (Sort s : master.getSorts()) {
            Set<Sort> children = directChildSorts(s, master.getSorts());
            for (Sort child : children) {
                if (!isSpecialSort(s)) {
                    // master.addAxiom(new SExpr("assert", new SExpr("subtype", SExprs.sortExpr(child), SExprs.sortExpr(s))));
                    // (assert (subtype s0 s1)) could be replaced by:
                    // (assert (forall ((u U)) (=> (instanceof u s0) (instanceof u s1))))
                    master.addAxiom(new SExpr("assert", subtypeHelper(child, s)));
                }
                for (Sort otherChild : children) {
                    if (!(child.equals(otherChild)) && (!otherChild.name().toString().equals("Null"))
                            && (!child.name().toString().equals("Null"))) {
                        // SExpr st = new SExpr("subtype", SExprs.sortExpr(child), SExprs.sortExpr(otherChild));
                        // master.addAxiom(new SExpr("assert", new SExpr("not", st)));
                        // (assert (not (subtype s0 s1))) could be replaced by:
                        // (assert (not (forall ((u U)) (=> (instanceof u s0) (instanceof u s1)))))
                        SExpr st = subtypeHelper(child, otherChild);
                        master.addAxiom(new SExpr("assert", new SExpr("not", st)));
                    }
                }
            }
        }
        // if sort has no direct parents, make it a child of any
        for (Sort s : master.getSorts()) {
            if (!(s instanceof NullSort) && !(s.equals(Sort.ANY)) && !(s.equals(Sort.FORMULA))) {
                if (s.extendsSorts().isEmpty()) {
                    // master.addAxiom(new SExpr("assert", new SExpr("subtype", SExprs.sortExpr(s), SExprs.sortExpr(Sort.ANY))));
                    // (assert (subtype s0 sort_any)) could be replaced by
                    // (assert (forall ((u U)) (=> (instanceof u s0) (instanceof u sort_any))))
                    master.addAxiom(new SExpr("assert", subtypeHelper(s, Sort.ANY)));
                }
            }
        }
    }

    private static SExpr subtypeHelper(Sort child, Sort otherChild) {
        SExpr ante = new SExpr("instanceof", Type.BOOL, new SExpr("u"),
            SExprs.sortExpr(child));
        SExpr cons = new SExpr("instanceof", Type.BOOL, new SExpr("u"),
            SExprs.sortExpr(otherChild));
        SExpr impl = SExprs.imp(ante, cons);
        SExpr vars = new SExpr(new SExpr("u", Type.NONE, "U"));
        return new SExpr("forall", Type.BOOL, vars, impl);
    }

    /**
     * @param parent the (possible) parent sort
     * @param child the (possible) child sort
     * @return true iff parent is a direct parent sort of child
     */
    private boolean isDirectParentOf(Sort parent, Sort child) {
        return child.extendsSorts(services).contains(parent);
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

    private Set<Sort> collectAllSubtypes(Sort s, Set<Sort> sorts) {
        Set<Sort> res = new HashSet<>();
        for (Sort child : sorts) {
            if (child != s && child.extendsTrans(s)) {
                res.add(child);
            }
        }
        return res;
    }

    static boolean isSpecialSort(Sort sort) {
        return isNullSort(sort) || isEmbeddedSort(sort);
    }

    static boolean isEmbeddedSort(Sort sort) {
        return EMBEDDED_SORTS.contains(sort.toString());
    }

    static boolean isNullSort(Sort sort) {
        return sort.name().toString().equals(NULL_SORT);
    }
}
