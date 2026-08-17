/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.logic.sort.ProxySort;

import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Generic removing lemma generator adds the default implementation only that all
 * {@link GenericSort}s are replaced to equally named {@link ProxySort}s.
 *
 * <p>
 * This is done since the resulting term is to be used as a proof obligation in which generic sorts
 * must not appear; proxy sorts, however, may.
 *
 * For every generic sort, precisely one proxy sort is introduced.
 */
public class GenericRemovingLemmaGenerator extends DefaultLemmaGenerator {
    /**
     * The map from generic sorts to proxy sorts.
     */
    private final Map<Sort, Sort> sortMap = new HashMap<>();

    /**
     * {@inheritDoc}
     * <p>
     * The generic removing implementation replaces parametric functions if their sort argument
     * is a generic sort.
     */
    @Override
    protected Operator replaceOp(Operator op, TermServices services) {
        if (op instanceof ParametricFunctionInstance pfi) {
            List<GenericArgument> newArgs = new LinkedList<>();
            boolean changed = false;
            for (var arg : pfi.getArgs()) {
                final var sort = arg.sort();
                if (sort.containsGenericSort()) {
                    newArgs.add(new GenericArgument(replaceSort(sort, services)));
                    changed = true;
                } else {
                    newArgs.add(arg);
                }
            }
            if (changed) {
                op = ParametricFunctionInstance.get(pfi.getBase(),
                    ImmutableList.fromList(newArgs), (Services) services);
            }
        }

        return op;
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * The generic removing implementation replaces generic sorts by equally named proxy sorts.
     */
    @Override
    protected Sort replaceSort(Sort sort, TermServices services) {
        Sort cached = sortMap.get(sort);
        if (cached != null) {
            return cached;
        }
        if (sort instanceof GenericSort gs) {
            Sort declared = services.getNamespaces().sorts().lookup(gs.name());
            if (declared instanceof ProxySort declaredProxy) {
                sortMap.put(gs, declaredProxy);
                return declaredProxy;
            }
            ImmutableSet<Sort> extSorts = replaceSorts(gs.extendsSorts(), services);
            ProxySort result = new ProxySort(gs.name(), extSorts);
            sortMap.put(gs, result);
            return result;
        } else if (sort instanceof ParametricSortInstance psi && psi.containsGenericSort()) {
            List<GenericArgument> newArgs = new ArrayList<>(psi.getArgs().size());
            for (var arg : psi.getArgs()) {
                newArgs.add(new GenericArgument(replaceSort(arg.sort(), services)));
            }
            ParametricSortInstance newSort = ParametricSortInstance.get(psi.getBase(),
                ImmutableList.fromList(newArgs), (Services) services);
            sortMap.put(sort, newSort);
            return newSort;
        } else {
            return sort;
        }
    }

    /**
     * Replace sorts.
     *
     * @param extendsSorts the extends sorts
     * @param services the services
     * @return the immutable set
     */
    private ImmutableSet<Sort> replaceSorts(ImmutableSet<Sort> extendsSorts,
            TermServices services) {
        ImmutableSet<Sort> result = DefaultImmutableSet.nil();
        for (Sort sort : extendsSorts) {
            result = result.add(replaceSort(sort, services));
        }
        return result;
    }
}
