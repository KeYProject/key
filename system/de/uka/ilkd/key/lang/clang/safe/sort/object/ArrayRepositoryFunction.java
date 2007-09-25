package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.common.operator.BaseRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rigid array repository function <code>{parent}::&lt;lookup&gt; : int, int -> {parent}</code>.
 * @author oleg.myrk@gmail.com
 */
public class ArrayRepositoryFunction extends BaseRigidOperator implements IFunction {
        private final UnsizedArraySort parent;
                
        /**
         * Creates the repository function.
         * @param parent
         * @param intSort
         */
        public ArrayRepositoryFunction(UnsizedArraySort parent, Sort intSort) {
                super(  new Name(parent.name() + "::<lookup>"),
                        parent,
                        new Sort[] { intSort, intSort }
                        );
                this.parent = parent;
        }
        
        /**
         * Returns the sort this function belongs to.
         * @return
         */                
        public UnsizedArraySort getUnsizedArraySort() {
                return parent;
        }
}
