/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import java.util.Map;
import java.util.Objects;
import java.util.WeakHashMap;
import java.util.function.Function;

import org.jspecify.annotations.NullMarked;
import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

@NullMarked
public class ParametricSortInstance extends AbstractSort {
    private static final Map<ParametricSortInstance, ParametricSortInstance> CACHE =
        new WeakHashMap<>();

    private final ImmutableList<Sort> parameters;

    private final ParametricSortDeclaration base;

    private final ImmutableSet<Sort> extendsSorts;

    public static ParametricSortInstance get(ParametricSortDeclaration base,
            ImmutableList<Sort> parameters) {
        ParametricSortInstance sort =
            new ParametricSortInstance(base, parameters);
        ParametricSortInstance cached = CACHE.get(sort);
        if (cached != null) {
            return cached;
        } else {
            CACHE.put(sort, sort);
            return sort;
        }
    }

    // This must only be called in #get, which ensures that the cache is used.
    private ParametricSortInstance(ParametricSortDeclaration base, ImmutableList<Sort> parameters) {
        super(makeName(base, parameters), base.isAbstract(), base.getDocumentation(), base.getOrigin());

        this.extendsSorts = computeExt(base, parameters);
        this.base = base;
        this.parameters = parameters;
    }

    private static ImmutableSet<Sort> computeExt(ParametricSortDeclaration base,
            ImmutableList<Sort> parameters) {
        ImmutableSet<Sort> result = DefaultImmutableSet.nil();

        // 1. extensions by base sort
        ImmutableSet<Sort> baseExt = base.getExtendedSorts();
        if (!baseExt.isEmpty()) {
            Function<Sort, Sort> inster = base.getInstantiator(parameters);
            for (Sort s : baseExt) {
                result = result.add(inster.apply(s));
            }
        }

        // 2. extensions by variances
        ImmutableList<ParametricSortDeclaration.SortParameter> cov = base.getParameters();
        int number = 0;
        for (ParametricSortDeclaration.SortParameter parameter : base.getParameters()) {
            switch(parameter.variance()) {
                case COVARIANT -> {
                    // take all bases of that arg and add the modified sort as ext class
                    /* for (Sort s : parameter.genericSort().extendsSorts()) {
                        ImmutableList<Sort> newArgs = parameters.replace(number, s);
                        result = result.add(ParametricSortInstance.get(base, newArgs));
                    } */
//                    throw new UnsupportedOperationException(
//                            "Covariance currently not supported");
                }

                case CONTRAVARIANT -> throw new UnsupportedOperationException(
                        "Contravariance currently not supported");

                case INVARIANT -> {
                    /* Nothing to be done */}
            }
        }
        return result;
    }

    private static Name makeName(ParametricSortDeclaration base, ImmutableList<Sort> parameters) {
        // The [ ] are produced by the list's toString method.
        return new Name(base.name() + "<" + parameters + ">");
    }

    public ParametricSortDeclaration getBase() {
        return base;
    }

    public ImmutableList<Sort> getParameters() {
        return parameters;
    }

    public ParametricSortInstance map(Function<Sort, Sort> f) {
        ImmutableList<Sort> newParameters = parameters.map(f);
        // The cache ensures that no unnecessary duplicates are kept.
        return get(base, newParameters);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        ParametricSortInstance that = (ParametricSortInstance) o;
        return Objects.equals(parameters, that.parameters) &&
                base == that.base;
    }

    @Override
    public int hashCode() {
        return Objects.hash(parameters, base);
    }

    @Override
    public ImmutableSet<Sort> extendsSorts() {
        return extendsSorts;
    }

    @Override
    public boolean extendsTrans(Sort sort) {
        return sort == this || extendsSorts()
                .exists((Sort superSort) -> superSort == sort || superSort.extendsTrans(sort));
    }

    public static Sort instantiate(GenericSort genericSort, Sort instantiation, Sort toInstantiate) {
        if(genericSort == toInstantiate) {
            return instantiation;
        } else if(toInstantiate instanceof ParametricSortInstance psort) {
            return psort.instantiate(genericSort, instantiation);
        } else {
            return toInstantiate;
        }
    }

    public Sort instantiate(GenericSort template, Sort instantiation) {
        ImmutableList<Sort> newParameters = parameters.map(s -> instantiate(template, instantiation, s));
        return get(base, newParameters);
    }
}
