package org.keyproject.key.api.data;

import de.uka.ilkd.key.logic.op.Function;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (15.10.23)
 */
public record FunctionDesc(String name, String sort, SortDesc retSort, List<SortDesc> argSorts, boolean rigid,
                           boolean unique, boolean skolemConstant) {
    public static FunctionDesc from(Function fn) {
        return new FunctionDesc(fn.name().toString(), fn.proofToString(),
                SortDesc.from(fn.sort()),
                fn.argSorts().stream().map(SortDesc::from).toList(),
                fn.isRigid(),
                fn.isUnique(),
                fn.isSkolemConstant());
    }
}
