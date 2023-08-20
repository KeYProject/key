/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.Name;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * The objects of this class represent array sorts (in the sense of *Java* arrays). There can be one
 * such sort for every element sort; however, the array sorts are only created lazily on demand.
 * <p>
 * More precisely, there can be one array sort for every pair (element sort, element type); i.e.,
 * there can be several array sorts for the same element sort, distinguished by their element
 * *type*. This is used for the integer types of Java: these are all mapped to the sort "int" (i.e.,
 * the mathematical integers), but we have different array sorts int[], byte[], char[], short[] and
 * long[], all storing mathematical integers.
 */
public final class ArraySort extends AbstractSort {

    private static final WeakHashMap<SortKey, WeakReference<ArraySort>> aSH =
        new WeakHashMap<>();

    /**
     * keeping this key is important to prevent for too early hashmap removal
     */
    private final SortKey sk;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private ArraySort(ImmutableSet<Sort> extendsSorts, SortKey sk) {
        super(new Name((sk.elemType != null ? sk.elemType.getName() : sk.elemSort.name()) + "[]"),
            extendsSorts, false);

        if (extendsSorts.isEmpty()) {
            throw new IllegalArgumentException("An ArraySort extends typically three sorts"
                + " (java.lang.Object, java.lang.Serializable, java.lang.Cloneable). You gave 0 sorts.");
        }

        if (sk.elemSort instanceof GenericSort) {
            throw new IllegalArgumentException(
                "array sorts with generic element sorts currently not supported");
        }

        this.sk = sk;
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static ImmutableSet<Sort> getArraySuperSorts(Sort elemSort, Sort objectSort,
            Sort cloneableSort, Sort serializableSort) {
        ImmutableSet<Sort> result = DefaultImmutableSet.nil();
        ImmutableSet<Sort> elemDirectSuperSorts = elemSort.extendsSorts();

        if (elemDirectSuperSorts.size() == 1
                && elemDirectSuperSorts.iterator().next().equals(Sort.ANY)) {
            if (objectSort != null) {
                result = result.add(objectSort);
            }
            if (cloneableSort != null) {
                result = result.add(cloneableSort);
            }
            if (serializableSort != null) {
                result = result.add(serializableSort);
            }
        } else {
            for (Sort s : elemDirectSuperSorts) {
                result = result.add(getArraySort(s, objectSort, cloneableSort, serializableSort));
            }
        }

        return result;
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Returns the ArraySort to the given element sort and element type. This method ensures that
     * only one ArraySort-object exists for each array sort.
     */
    public static ArraySort getArraySort(Sort elemSort, Type elemType, Sort objectSort,
            Sort cloneableSort, Sort serializableSort) {
        if (elemType != PrimitiveType.JAVA_BYTE && elemType != PrimitiveType.JAVA_CHAR
                && elemType != PrimitiveType.JAVA_INT && elemType != PrimitiveType.JAVA_LONG
                && elemType != PrimitiveType.JAVA_SHORT) {
            elemType = null;
        }
        // this wrapper is required as some element sorts are shared among
        // several environments (int, boolean)
        final SortKey sortKey =
            new SortKey(elemSort, elemType, objectSort, cloneableSort, serializableSort);
        WeakReference<ArraySort> ref = aSH.get(sortKey);
        ArraySort as = ref != null ? ref.get() : null;

        if (as == null) {
            ImmutableSet<Sort> localExtendsSorts =
                getArraySuperSorts(elemSort, objectSort, cloneableSort, serializableSort);
            as = new ArraySort(localExtendsSorts, sortKey);
            aSH.put(sortKey, new WeakReference<>(as));
        }
        return as;
    }


    public static ArraySort getArraySort(Sort elemSort, Sort objectSort, Sort cloneableSort,
            Sort serializableSort) {
        return getArraySort(elemSort, null, objectSort, cloneableSort, serializableSort);
    }


    /**
     * returns elemSort([])^n.
     */
    public static Sort getArraySortForDim(Sort elemSort, Type elemType, int n, Sort objectSort,
            Sort cloneableSort, Sort serializableSort) {
        assert n > 0;
        Sort result = getArraySort(elemSort, elemType, objectSort, cloneableSort, serializableSort);

        while (n > 1) {
            result = getArraySort(result, objectSort, cloneableSort, serializableSort);
            n--;
        }
        return result;
    }


    /**
     * returns the element sort of the array
     */
    public Sort elementSort() {
        return sk.elemSort;
    }


    private static final class SortKey {
        final Sort elemSort;
        final Type elemType;
        final Sort javaLangObjectSort;
        final Sort javaLangSerializable;
        final Sort javaLangCloneable;

        public SortKey(Sort elemSort, Type elemType, Sort javaLangObjectSort,
                Sort javaLangCloneable, Sort javaLangSerializable) {
            this.elemSort = elemSort;
            this.elemType = elemType;
            this.javaLangObjectSort = javaLangObjectSort;
            this.javaLangCloneable = javaLangCloneable;
            this.javaLangSerializable = javaLangSerializable;
        }


        public boolean equals(Object o) {
            if (!(o instanceof SortKey)) {
                return false;
            }
            final SortKey sk = (SortKey) o;
            return elemSort == sk.elemSort && elemType == sk.elemType
                    && javaLangObjectSort == sk.javaLangObjectSort
                    && javaLangSerializable == sk.javaLangSerializable
                    && javaLangCloneable == sk.javaLangCloneable;
        }


        public int hashCode() {
            return elemSort.hashCode() + (elemType == null ? 0 : 31 * elemType.hashCode())
                    + (javaLangCloneable == null ? 0 : 31 * javaLangCloneable.hashCode())
                    + (javaLangObjectSort == null ? 0 : 17 * javaLangObjectSort.hashCode())
                    + (javaLangSerializable == null ? 0 : 3 * javaLangSerializable.hashCode());
        }
    }
}
