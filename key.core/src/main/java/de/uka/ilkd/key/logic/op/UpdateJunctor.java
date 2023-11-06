/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


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
        for (int i = 0; i < arity; i++) {
            result[i] = Sort.UPDATE;
        }
        return result;
    }


    private UpdateJunctor(Name name, int arity) {
        super(name, createUpdateSortArray(arity), Sort.UPDATE, false);
    }
}
