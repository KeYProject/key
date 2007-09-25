package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.lang.common.operator.BaseRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rigid constant <code>{parent}::fromInt : int -> {parent}</code>.
 * @author oleg.myrk@gmail.com
 */
public class FromIntFunction extends BaseRigidOperator implements IFunction {        
        private final IntegerSort parent;
        
        public FromIntFunction(IntegerSort parent, Sort intSort) {
                super(  new Name(parent.name() + "::fromInt"),
                        parent,
                        new Sort[]{intSort}
                        );
                this.parent = parent;
        }
        
        /**
         * Returns the integer sort this function belongs to.
         * @return
         */
        public IntegerSort getIntegerSort() {
                return parent;
        }
}
