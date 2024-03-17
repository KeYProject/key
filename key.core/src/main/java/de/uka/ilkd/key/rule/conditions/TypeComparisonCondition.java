/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import java.util.Map;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.ProxySort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.sort.Sort;


/**
 * General varcond for checking relationships between types of schema variables.
 */
public final class TypeComparisonCondition extends VariableConditionAdapter {

    public enum Mode {
        NOT_SAME, /* checks if sorts are not same */
        SAME, /* checks if sorts are same */
        IS_SUBTYPE, /* checks subtype relationship */
        NOT_IS_SUBTYPE, /* checks subtype relationship */
        STRICT_SUBTYPE, /* checks for strict subtype */
        DISJOINTMODULONULL
    } /* checks if sorts are disjoint */

    private final Mode mode;
    private final TypeResolver fst;
    private final TypeResolver snd;


    /**
     * creates a condition that checks if the declaration types of the schemavariable's
     * instantiations are unequal
     *
     * @param fst one of the SchemaVariable whose type is checked
     * @param snd one of the SchemaVariable whose type is checked
     * @param mode an int encoding if testing of not same or not compatible
     */
    public TypeComparisonCondition(TypeResolver fst, TypeResolver snd, Mode mode) {
        this.fst = fst;
        this.snd = snd;
        this.mode = mode;
    }


    public TypeResolver getFirstResolver() {
        return fst;
    }


    public TypeResolver getSecondResolver() {
        return snd;
    }


    public Mode getMode() {
        return mode;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute subst, SVInstantiations svInst,
            Services services) {

        if (!fst.isComplete(var, subst, svInst, services)
                || !snd.isComplete(var, subst, svInst, services)) {
            // not yet complete
            return true;
        }
        Sort fstSort = fst.resolveSort(var, subst, svInst, services);
        Sort sndSort = snd.resolveSort(var, subst, svInst, services);

        return checkSorts(fstSort, sndSort, services);
    }


    private boolean checkSorts(final Sort fstSort, final Sort sndSort, final Services services) {

        boolean proxy1 = fstSort instanceof ProxySort;
        boolean proxy2 = sndSort instanceof ProxySort;

        if (!proxy1 && !proxy2) {
            // This is the standard case where no proxy sorts are involved
            return switch (mode) {
            case SAME -> fstSort == sndSort;
            case NOT_SAME -> fstSort != sndSort;
            case IS_SUBTYPE -> fstSort.extendsTrans(sndSort);
            case STRICT_SUBTYPE -> fstSort != sndSort && fstSort.extendsTrans(sndSort);
            case NOT_IS_SUBTYPE -> !fstSort.extendsTrans(sndSort);
            case DISJOINTMODULONULL -> checkDisjointness(fstSort, sndSort, services);
            };
        } else {
            switch (mode) {
            case SAME -> {
                return fstSort == sndSort;
            }
            case IS_SUBTYPE -> {
                if (proxy2) {
                    return false;
                }
                // If one of the extended types is a subtype to sndSort, then so
                // is the proxy sort.
                assert proxy1;
                for (Sort extSort : fstSort.extendsSorts()) {
                    if (extSort.extendsTrans(sndSort)) {
                        return true;
                    }
                }
                return false;
            }
            case STRICT_SUBTYPE -> {
                if (proxy2) {
                    return false;
                }
                // If one of the extended types is a subtype to sndSort, then so
                // is the proxy sort.
                assert proxy1;
                for (Sort extSort : fstSort.extendsSorts()) {
                    if (extSort != sndSort && extSort.extendsTrans(sndSort)) {
                        return true;
                    }
                }
                return false;
            }
            case NOT_SAME, DISJOINTMODULONULL, NOT_IS_SUBTYPE -> {
                // There are cases where - based on the bounds - true could be returned.
                // Implement them if needed. There is the Null type to consider as subtype.
                return false;
            }
            }
        }

        assert false : "All cases should have been covered";
        return false;
    }

    private static Boolean lookupInCache(Sort s1, Sort s2, ServiceCaches caches) {
        Boolean result = null;

        final Map<Sort, Map<Sort, Boolean>> disjointnessCache = caches.getDisjointnessCache();
        Map<Sort, Boolean> map;
        synchronized (disjointnessCache) {
            map = disjointnessCache.get(s1);
        }
        if (map != null) {
            synchronized (map) {
                result = map.get(s2);
            }
        }

        if (result == null) {
            synchronized (disjointnessCache) {
                map = disjointnessCache.get(s2);
            }
            if (map != null) {
                synchronized (map) {
                    result = map.get(s1);
                }
            }
        }
        return result;
    }


    private static void putIntoCache(Sort s1, Sort s2, boolean b, ServiceCaches caches) {
        final Map<Sort, Map<Sort, Boolean>> disjointnessCache = caches.getDisjointnessCache();
        Map<Sort, Boolean> map;
        synchronized (disjointnessCache) {
            map = disjointnessCache.get(s1);
        }

        if (map == null) {
            map = new WeakHashMap<>();
            map.put(s2, b);
        } else {
            synchronized (map) {
                map.put(s2, b);
            }
        }

        synchronized (disjointnessCache) {
            disjointnessCache.put(s1, map);
        }
    }


    /**
     * Checks for disjointness modulo "null".
     */
    private boolean checkDisjointness(Sort fstSort, Sort sndSort, Services services) {
        // sorts identical?
        if (fstSort == sndSort) {
            return false;
        }

        // result cached?
        Boolean result = lookupInCache(fstSort, sndSort, services.getCaches());

        // if not, compute it
        if (result == null) {
            final JavaInfo javaInfo = services.getJavaInfo();

            // array sorts are disjoint if their element sorts are disjoint
            Sort fstElemSort = fstSort;
            Sort sndElemSort = sndSort;
            while (fstElemSort instanceof ArraySort && sndElemSort instanceof ArraySort) {
                fstElemSort = ((ArraySort) fstElemSort).elementSort();
                sndElemSort = ((ArraySort) sndElemSort).elementSort();
            }

            // object sorts?
            final Sort objectSort = services.getJavaInfo().objectSort();
            boolean fstElemIsObject = fstElemSort.extendsTrans(objectSort);
            boolean sndElemIsObject = sndElemSort.extendsTrans(objectSort);

            // try to get KeYJavaTypes (only works for types existing in program)
            final KeYJavaType fstKJT = javaInfo.getKeYJavaType(fstSort);
            final KeYJavaType sndKJT = javaInfo.getKeYJavaType(sndSort);

            if (fstElemIsObject && sndElemIsObject && !(fstElemSort instanceof ArraySort)
                    && !(sndElemSort instanceof ArraySort)
                    && (fstKJT != null && fstKJT.getJavaType() instanceof InterfaceDeclaration
                            || sndKJT != null
                                    && sndKJT.getJavaType() instanceof InterfaceDeclaration)) {
                // be conservative wrt. modularity: program extensions may add
                // new subtypes between object sorts, if none of them is
                // an array sort and at least one of them is an interface sort
                result = false;
            } else {
                // otherwise, we just check whether *currently* there is
                // some common subsort
                result = true;
                for (Sort n : services.getNamespaces().sorts().allElements()) {
                    final Sort s = n;
                    if (!(s instanceof NullSort) && s.extendsTrans(fstSort)
                            && s.extendsTrans(sndSort)) {
                        result = false;
                        break;
                    }
                }
            }

            putIntoCache(fstSort, sndSort, result, services.getCaches());
        }

        return result;
    }


    @Override
    public String toString() {
        return switch (mode) {
        case SAME -> "\\same(" + fst + ", " + snd + ")";
        case NOT_SAME -> "\\not\\same(" + fst + ", " + snd + ")";
        case IS_SUBTYPE -> "\\sub(" + fst + ", " + snd + ")";
        case STRICT_SUBTYPE -> "\\strict\\sub(" + fst + ", " + snd + ")";
        case NOT_IS_SUBTYPE -> "\\not\\sub(" + fst + ", " + snd + ")";
        case DISJOINTMODULONULL -> "\\disjointModuloNull(" + fst + ", " + snd + ")";
        default -> "invalid type comparison mode";
        };
    }
}
