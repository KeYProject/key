/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import java.util.Arrays;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;

import org.jspecify.annotations.NonNull;


/**
 * Class of update junctor operators, i.e., operators connecting a given number of updates to create
 * another update. There are currently two such operators: the empty update "skip" and the parallel
 * update connector "|".
 */
public final class UpdateJunctor extends AbstractSortedOperator {

    public static final UpdateJunctor SKIP = new UpdateJunctor(new Name("skip"), 0);

    public static final UpdateJunctor PARALLEL_UPDATE =
        new UpdateJunctor(new Name("parallel-upd"), 2);


    private static Sort[] createUpdateSortArray(int arity) {
        Sort[] result = new Sort[arity];
        Arrays.fill(result, RustyDLTheory.UPDATE);
        return result;
    }


    private UpdateJunctor(Name name, int arity) {
        super(name, createUpdateSortArray(arity), RustyDLTheory.UPDATE, Modifier.NONE);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("UpdateJunctor " + name() + " has no children");
    }
}
