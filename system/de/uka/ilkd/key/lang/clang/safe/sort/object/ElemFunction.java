package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.common.operator.BaseRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rigid function <code>elem : {parent}, int -> {parent.elemSort}</code>.
 * @author oleg.myrk@gmail.com
 */
public class ElemFunction extends BaseRigidOperator implements IFunction {
        private final UnsizedArraySort parent;  
        
        public ElemFunction(UnsizedArraySort parent, Sort intSort) {
                super(  new Name(parent.name() + "::elem"),
                        parent.getElemSort(),
                        new Sort[] {parent, intSort}
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