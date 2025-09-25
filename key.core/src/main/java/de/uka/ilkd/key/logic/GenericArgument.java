/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

/// An argument for a [ParametricSortInstance] or [ParametricFunctionInstance].
public record GenericArgument(Sort sort) implements TerminalSyntaxElement {
    @Override
    public @NonNull String toString() {
        return sort.toString();
    }

    public GenericArgument instantiate(SVInstantiations svInst, Services services) {
        if (sort instanceof GenericSort gs) {
            return new GenericArgument(
                svInst.getGenericSortInstantiations().getRealSort(gs, services));
        } else if (sort instanceof ParametricSortInstance psi) {
            ImmutableList<GenericArgument> args = ImmutableSLList.nil();

            for (int i = psi.getArgs().size() - 1; i >= 0; i--) {
                args = args.prepend(psi.getArgs().get(i).instantiate(svInst, services));
            }

            return new GenericArgument(ParametricSortInstance.get(psi.getBase(), args, services));
        } else {
            return this;
        }
    }
}
