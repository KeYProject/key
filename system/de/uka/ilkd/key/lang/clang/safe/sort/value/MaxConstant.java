package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.lang.common.operator.BaseRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rigid constant <code>{parent}::MAX : int</code>.
 * @author oleg.myrk@gmail.com
 */
public class MaxConstant extends BaseRigidOperator implements IFunction {        
        private final IntegerSort parent;
        
        public MaxConstant(IntegerSort parent, Sort intSort) {
                super(  new Name(parent.name() + "::MAX"),
                        intSort,
                        new Sort[0]
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
