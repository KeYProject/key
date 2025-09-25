/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.GenericParameter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/// Concrete sort of a parametric sort.
public final class ParametricSortInstance extends AbstractSort {
    private static final Map<ParametricSortInstance, ParametricSortInstance> CACHE =
        new WeakHashMap<>();

    private final ImmutableList<GenericArgument> args;
    private final ParametricSortDecl base;
    private final ImmutableSet<Sort> extendsSorts;

    /// Returns the sort of `decl` instantiated with the arguments `arg`. If necessary, a new object
    /// is created.
    public static ParametricSortInstance get(ParametricSortDecl base,
            ImmutableList<GenericArgument> args, Services services) {
        assert args.size() == base.getParameters().size();
        ParametricSortInstance sort =
            new ParametricSortInstance(base, args);
        ParametricSortInstance cached = CACHE.get(sort);
        if (cached != null) {
            return cached;
        } else {
            CACHE.put(sort, sort);
            if (!sort.containsGenericSort())
                services.getNamespaces().sorts().addSafely(sort);
            return sort;
        }
    }

    /// This must only be called in [ParametricSortInstance#get], which ensures that the cache is
    /// used.
    private ParametricSortInstance(ParametricSortDecl base, ImmutableList<GenericArgument> args) {
        super(makeName(base, args), base.isAbstract());

        this.extendsSorts = ImmutableSet.singleton(JavaDLTheory.ANY);
        this.base = base;
        this.args = args;
    }

    private static Name makeName(ParametricSortDecl base,
            ImmutableList<GenericArgument> parameters) {
        // The [ ] are produced by the list's toString method.
        return new Name(base.name() + "<" + parameters + ">");
    }

    private static ImmutableSet<Sort> computeExt(ParametricSortDecl base,
            ImmutableList<GenericArgument> args, Services services) {
        ImmutableSet<Sort> result = DefaultImmutableSet.nil();

        // 1. extensions by base sort
        ImmutableSet<Sort> baseExt = base.getExtendedSorts();
        if (!baseExt.isEmpty()) {
            for (Sort s : baseExt) {
                result =
                    result.add(instantiate(s, getInstMap(base, args),
                        services));
            }
        }

        // 2. extensions by variances
        ImmutableList<GenericParameter> cov = base.getParameters();
        int number = 0;
        for (GenericParameter parameter : base.getParameters()) {
            switch (parameter.variance()) {
                case COVARIANT -> {
                    // take all bases of that arg and add the modified sort as ext class
                    /*
                     * for (Sort s : parameter.genericSort().extendsSorts()) {
                     * ImmutableList<Sort> newArgs = args.replace(number, s);
                     * result = result.add(ParametricSortInstance.get(base, newArgs));
                     * }
                     */
                    // throw new UnsupportedOperationException(
                    // "Covariance currently not supported");
                }
                case CONTRAVARIANT -> throw new UnsupportedOperationException(
                    "Contravariance currently not supported");

                case INVARIANT -> {
                    /* Nothing to be done */}
            }
        }

        return result;
    }

    public ParametricSortDecl getBase() {
        return base;
    }

    public ImmutableList<GenericArgument> getArgs() {
        return args;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        ParametricSortInstance that = (ParametricSortInstance) o;
        return Objects.equals(args, that.args) &&
                base == that.base;
    }

    @Override
    public int hashCode() {
        return Objects.hash(args, base);
    }

    @Override
    public @NonNull ImmutableSet<Sort> extendsSorts() {
        return extendsSorts;
    }

    @Override
    public boolean extendsTrans(@NonNull Sort sort) {
        return sort == this || extendsSorts()
                .exists((Sort superSort) -> superSort == sort || superSort.extendsTrans(sort));
    }

    /// Compute an instantiation mapping.
    private static Map<GenericSort, GenericArgument> getInstMap(ParametricSortDecl base,
            ImmutableList<GenericArgument> args) {
        var map = new HashMap<GenericSort, GenericArgument>();
        for (int i = 0; i < base.getParameters().size(); i++) {
            var param = base.getParameters().get(i);
            var arg = args.get(i);
            map.put(param.sort(), arg);
        }
        return map;
    }

    public static Sort instantiate(GenericSort genericSort, Sort instantiation,
            Sort toInstantiate, Services services) {
        if (genericSort == toInstantiate) {
            return instantiation;
        } else if (toInstantiate instanceof ParametricSortInstance psort) {
            return psort.instantiate(genericSort, instantiation, services);
        } else {
            return toInstantiate;
        }
    }

    /// Instantiate a sort that may be or contain generic sorts with `map`.
    public static Sort instantiate(Sort sort, Map<GenericSort, GenericArgument> map,
            Services services) {
        if (sort instanceof GenericSort gs) {
            var arg = map.get(gs);
            return arg == null ? gs : arg.sort();
        } else if (sort instanceof ParametricSortInstance psi) {
            var base = psi.getBase();
            ImmutableList<GenericArgument> args = ImmutableSLList.nil();
            for (int i = psi.getArgs().size() - 1; i >= 0; i--) {
                var psiArg = psi.getArgs().get(i);
                args = args.prepend(new GenericArgument(instantiate(psiArg.sort(), map, services)));
            }
            return ParametricSortInstance.get(base, args, services);
        } else {
            return sort;
        }
    }

    public ParametricSortInstance instantiate(GenericSort template, Sort instantiation,
            Services services) {
        ImmutableList<GenericArgument> newParameters =
            args.map(
                s -> new GenericArgument(instantiate(template, instantiation, s.sort(), services)));
        return get(base, newParameters, services);
    }

    /// Whether this sort is complete when instantiated with `instMap`.
    public boolean isComplete(SVInstantiations instMap) {
        for (GenericArgument arg : args) {
            var sort = arg.sort();
            if (sort instanceof ParametricSortInstance psi) {
                if (!psi.isComplete(instMap))
                    return false;
            } else if (sort instanceof GenericSort gs) {
                if (instMap.getGenericSortInstantiations().getInstantiation(gs) == null)
                    return false;
            }
        }
        return true;
    }

    /// Get the sort if this parametric sort with all generics instantiated with `instMap`.
    public Sort resolveSort(SVInstantiations instMap, Services services) {
        ImmutableList<GenericArgument> newArgs = ImmutableSLList.nil();
        for (int i = args.size() - 1; i >= 0; i--) {
            GenericArgument arg = args.get(i);
            var sort = arg.sort();
            if (sort instanceof ParametricSortInstance psi) {
                newArgs =
                    newArgs.prepend(
                        new GenericArgument(psi.resolveSort(instMap, services)));
            } else if (sort instanceof GenericSort gs) {
                newArgs = newArgs.prepend(
                    new GenericArgument(
                        instMap.getGenericSortInstantiations().getInstantiation(gs)));
            } else {
                newArgs = newArgs.prepend(arg);
            }
        }
        return get(base, newArgs, services);
    }

    /// Whether this sort contains generic sorts.
    public boolean containsGenericSort() {
        for (GenericArgument arg : args) {
            if (arg.sort() instanceof ParametricSortInstance psi && psi.containsGenericSort()) {
                return true;
            }
            if (arg.sort() instanceof GenericSort) {
                return true;
            }
        }
        return false;
    }
}
