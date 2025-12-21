/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.util.List;

import org.key_project.logic.op.Function;


/**
 * @author Alexander Weigl
 * @version 1 (15.10.23)
 */
public record FunctionDesc(String name, String sort, SortDesc retSort,
        List<SortDesc> argSorts,
        boolean rigid,
        boolean unique, boolean skolemConstant) implements KeYDataTransferObject {
    public static FunctionDesc from(Function fn) {
        return new FunctionDesc(fn.name().toString(), fn.sort().declarationString(),
            SortDesc.from(fn.sort()),
            fn.argSorts().stream().map(SortDesc::from).toList(),
            fn.isRigid(),
            fn.isUnique(),
            fn.isSkolemConstant());
    }
}
