/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.collection.ImmutableArray;

/**
 * Abstract base class for schema variables.
 */
public abstract class AbstractSV extends AbstractSortedOperator implements SchemaVariable {

    private final boolean isStrict;


    protected AbstractSV(Name name, ImmutableArray<Sort> argSorts, Sort sort, boolean isRigid,
            boolean isStrict) {
        super(name, argSorts, sort, isRigid);
        this.isStrict = isStrict;
    }


    protected AbstractSV(Name name, Sort[] argSorts, Sort sort, boolean isRigid, boolean isStrict) {
        this(name, new ImmutableArray<>(argSorts), sort, isRigid, isStrict);
    }


    protected AbstractSV(Name name, Sort sort, boolean isRigid, boolean isStrict) {
        this(name, (ImmutableArray<Sort>) null, sort, isRigid, isStrict);
    }


    protected final String toString(String sortSpec) {
        return name() + " (" + sortSpec + ")";
    }


    @Override
    public final boolean isStrict() {
        return isStrict;
    }
}
