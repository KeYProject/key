/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.util.collection.ImmutableArray;

/**
 * Objects of this class represent "observer" function or predicate symbols. Observer symbols are
 * used to
 * represent model functions as well as occurrences of
 * pure functions in specifications (via the subclass ProgramFunction). As they come from the Rust
 * program, both their parameter sorts and their result sorts always have an associated
 * KeYRustyType.
 * Observer symbols serve as the targets of contracts (i.e., as the subjects that the contracts are
 * about).
 */
public class ObserverFunction extends RFunction implements IObserverFunction {
    private final ImmutableArray<KeYRustyType> paramTypes;
    private final KeYRustyType type;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public ObserverFunction(String baseName, Sort sort, KeYRustyType type,
            ImmutableArray<KeYRustyType> paramTypes) {
        super(new Name(baseName), sort,
            getArgSorts(paramTypes));
        assert type == null || type.getSort() == sort;
        this.type = type;
        this.paramTypes = paramTypes;
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static Sort[] getArgSorts(ImmutableArray<KeYRustyType> paramTypes) {
        final int arity = paramTypes.size();

        final Sort[] result = new Sort[arity];

        for (int i = 0, n = paramTypes.size(); i < n; i++) {
            result[i] = paramTypes.get(i).getSort();
        }

        return result;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public KeYRustyType getType() {
        return type;
    }

    @Override
    public int getNumParams() {
        return paramTypes.size();
    }

    @Override
    public KeYRustyType getParamType(int i) {
        return paramTypes.get(i);
    }

    @Override
    public ImmutableArray<KeYRustyType> getParamTypes() {
        return paramTypes;
    }
}
