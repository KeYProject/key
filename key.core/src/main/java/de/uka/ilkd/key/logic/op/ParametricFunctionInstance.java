/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public class ParametricFunctionInstance extends JFunction {
    private static final Map<ParametricFunctionInstance, ParametricFunctionInstance> CACHE =
        new WeakHashMap<>();

    private final ImmutableList<GenericArgument> args;
    private final ParametricFunctionDecl base;

    public static ParametricFunctionInstance get(ParametricFunctionDecl decl,
            ImmutableList<GenericArgument> args, Services services) {
        assert args.size() == decl.getParameters().size();
        var instMap = getInstMap(decl, args);
        var argSorts = instantiate(decl, instMap, services);
        var sort = instantiate(decl.sort(), instMap, services);
        var fn = new ParametricFunctionInstance(decl, args, argSorts, sort);
        var cached = CACHE.get(fn);
        if (cached != null) {
            return cached;
        }
        CACHE.put(fn, fn);
        return fn;
    }

    private ParametricFunctionInstance(ParametricFunctionDecl base,
            ImmutableList<GenericArgument> args, ImmutableArray<Sort> argSorts, Sort sort) {
        super(makeName(base, args), sort, argSorts, base.getWhereToBind(), base.isUnique(),
            base.isRigid(),
            base.isSkolemConstant());
        this.base = base;
        this.args = args;
    }

    public ParametricFunctionDecl getBase() {
        return base;
    }

    public ImmutableList<GenericArgument> getArgs() {
        return args;
    }

    private static Name makeName(ParametricFunctionDecl base,
            ImmutableList<GenericArgument> parameters) {
        // The [ ] are produced by the list's toString method.
        return new Name(base.name() + "<" + parameters + ">");
    }

    private static ImmutableArray<Sort> instantiate(ParametricFunctionDecl base,
            Map<GenericSort, GenericArgument> instMap, Services services) {
        var baseArgSorts = base.argSorts();
        var argSorts = new Sort[baseArgSorts.size()];

        for (int i = 0; i < baseArgSorts.size(); i++) {
            var sort = baseArgSorts.get(i);
            argSorts[i] = instantiate(sort, instMap, services);
        }

        return new ImmutableArray<>(argSorts);
    }

    private static Map<GenericSort, GenericArgument> getInstMap(ParametricFunctionDecl base,
            ImmutableList<GenericArgument> args) {
        var map = new HashMap<GenericSort, GenericArgument>();
        for (int i = 0; i < base.getParameters().size(); i++) {
            var param = base.getParameters().get(i);
            var arg = args.get(i);
            map.put(param.sort(), arg);
        }
        return map;
    }

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

    @Override
    public int getChildCount() {
        return args.size();
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return Objects.requireNonNull(args.get(n));
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass())
            return false;
        ParametricFunctionInstance that = (ParametricFunctionInstance) o;
        return Objects.equals(args, that.args) && Objects.equals(base, that.base);
    }

    @Override
    public int hashCode() {
        return Objects.hash(args, base);
    }
}
