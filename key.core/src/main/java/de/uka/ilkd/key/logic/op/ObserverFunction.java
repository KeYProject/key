/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;


/**
 * Objects of this class represent "observer" function or predicate symbols. An observer symbol is a
 * symbol taking a heap array as its first argument, and an object as its second argument (unless it
 * is static). Observer symbols are used to represent JML model fields as well as occurrences of
 * pure methods in specifications (via the subclass ProgramMethod). As they come from the Java
 * program, both their parameter sorts and their result sorts always have an associated KeYJavaType.
 * Observer symbols serve as the targets of contracts (i.e., as the subjects that the contracts are
 * about).
 */
public class ObserverFunction extends JFunction implements IObserverFunction {

    private final KeYJavaType container;
    private final boolean isStatic;
    private final ImmutableArray<KeYJavaType> paramTypes;
    private final KeYJavaType type;
    private final int heapCount;
    private final int stateCount;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public ObserverFunction(String baseName, Sort sort, KeYJavaType type, Sort heapSort,
            KeYJavaType container, boolean isStatic, ImmutableArray<KeYJavaType> paramTypes,
            int heapCount, int stateCount) {
        super(createName(baseName, container), sort,
            getArgSorts(heapSort, container, isStatic, paramTypes, heapCount, stateCount));
        assert type == null || type.getSort() == sort;
        assert container != null;
        this.type = type;
        this.container = container;
        this.isStatic = isStatic;
        this.paramTypes = paramTypes;
        this.heapCount = heapCount;
        this.stateCount = stateCount;
    }

    public static ProgramElementName createName(String baseName, KeYJavaType container) {
        return new ProgramElementName(baseName, container.getSort().toString());
    }



    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static Sort[] getArgSorts(Sort heapSort, KeYJavaType container, boolean isStatic,
            ImmutableArray<KeYJavaType> paramTypes, int heapCount, int stateCount) {
        final int arity = paramTypes.size() + stateCount * heapCount + (isStatic ? 0 : 1);

        final Sort[] result = new Sort[arity];

        int offset;

        for (offset = 0; offset < stateCount * heapCount; offset++) {
            result[offset] = heapSort;
        }
        if (!isStatic) {
            result[offset] = container.getSort();
            assert result[offset] != null : "Bad KJT: " + container;
            offset++;
        }

        for (int i = 0, n = paramTypes.size(); i < n; i++) {
            result[i + offset] = paramTypes.get(i).getSort();
        }

        return result;
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.logic.op.IObserverFunction#getType()
     */
    @Override
    public final KeYJavaType getType() {
        return type;
    }


    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.logic.op.IObserverFunction#getContainerType()
     */
    @Override
    public final KeYJavaType getContainerType() {
        return container;
    }


    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.logic.op.IObserverFunction#isStatic()
     */
    @Override
    public final boolean isStatic() {
        return isStatic;
    }


    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.logic.op.IObserverFunction#getStateCount()
     */
    @Override
    public int getStateCount() {
        return stateCount;
    }

    @Override
    public int getHeapCount(Services services) {
        return heapCount;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.logic.op.IObserverFunction#getNumParams()
     */
    @Override
    public final int getNumParams() {
        return paramTypes.size();
    }


    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.logic.op.IObserverFunction#getParamType(int)
     */
    @Override
    public final KeYJavaType getParamType(int i) {
        return paramTypes.get(i);
    }


    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.logic.op.IObserverFunction#getParamTypes()
     */
    @Override
    public final ImmutableArray<KeYJavaType> getParamTypes() {
        return paramTypes;
    }

}
