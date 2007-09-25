package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.common.operator.BaseRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rigid function <code>size : {parent} -> int</code>.
 * @author oleg.myrk@gmail.com
 */
public class SizeFunction extends BaseRigidOperator implements IFunction {
        private final ArrayMarkerSort parent;  
        
        public SizeFunction(ArrayMarkerSort parent, Sort intSort) {
                super(  new Name("size"),
                        intSort,
                        new Sort[] { parent }
                        );
                this.parent = parent;
        }
        
        /**
         * Returns the sort this function belongs to.
         * @return
         */                
        public ArrayMarkerSort getArrayMarkerSort() {
                return parent;
        }        
}