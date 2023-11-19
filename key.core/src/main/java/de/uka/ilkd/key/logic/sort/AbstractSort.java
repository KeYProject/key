/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * Abstract base class for implementations of the Sort interface.
 */
public abstract class AbstractSort implements Sort {
    private final Name name;
    private final ImmutableSet<Sort> ext;
    private final boolean isAbstract;

    /**
     * Documentation for this sort given by the associated documentation comment.
     *
     * @see de.uka.ilkd.key.nparser.KeYParser.One_sort_declContext#doc
     */
    private final String documentation;

    /** Information of the origin of this sort */
    private final String origin;

    public AbstractSort(Name name,
            ImmutableSet<Sort> extendedSorts,
            boolean isAbstract,
            String documentation,
            String origin) {
        this.name = name;
        this.isAbstract = isAbstract;
        if (extendedSorts != null && extendedSorts.isEmpty()) {
            this.ext = DefaultImmutableSet.<Sort>nil().add(ANY);
        } else {
            this.ext = extendedSorts == null ? DefaultImmutableSet.<Sort>nil() : extendedSorts;
        }
        this.documentation = documentation;
        this.origin = origin;
    }

    @Override
    public final ImmutableSet<Sort> extendsSorts() {
        return ext;
    }

    @Override
    public final ImmutableSet<Sort> extendsSorts(Services services) {
        return extendsSorts();
    }


    @Override
    public final boolean extendsTrans(Sort sort) {
        if (sort == this) {
            return true;
        } else if (this == Sort.FORMULA || this == Sort.UPDATE) {
            return false;
        } else if (sort == Sort.ANY) {
            return true;
        }

        return extendsSorts()
                .exists((Sort superSort) -> superSort == sort || superSort.extendsTrans(sort));
    }


    @Override
    public final Name name() {
        return name;
    }


    @Override
    public final boolean isAbstract() {
        return isAbstract;
    }


    @Override
    public final SortDependingFunction getCastSymbol(TermServices services) {
        SortDependingFunction castFunction =
            SortDependingFunction.getFirstInstance(CAST_NAME, services);
        if (castFunction == null) {
            throw new IllegalStateException("Your namespaces does `cast' defined.");
        }
        SortDependingFunction result = castFunction.getInstanceFor(this, services);
        assert result.getSortDependingOn() == this && result.sort() == this;
        return result;
    }


    @Override
    public final SortDependingFunction getInstanceofSymbol(TermServices services) {
        SortDependingFunction result = SortDependingFunction
                .getFirstInstance(INSTANCE_NAME, services).getInstanceFor(this, services);
        assert result.getSortDependingOn() == this;
        return result;
    }


    @Override
    public final SortDependingFunction getExactInstanceofSymbol(TermServices services) {
        SortDependingFunction result = SortDependingFunction
                .getFirstInstance(EXACT_INSTANCE_NAME, services).getInstanceFor(this, services);
        assert result.getSortDependingOn() == this;
        return result;
    }


    @Override
    public final String toString() {
        return name.toString();
    }

    public String declarationString() {
        return name.toString();
    }

    @Nullable
    @Override
    public String getDocumentation() {
        return documentation;
    }

    @Nullable
    @Override
    public String getOrigin() {
        return origin;
    }
}
