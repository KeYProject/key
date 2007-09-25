package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.common.operator.BaseLocation;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;

/**
 * Rigid scalar value location <code>value : {ScalarSort.this} -> {ScalarSort.this.valueSort}</code>.
 * @author oleg.myrk@gmail.com
 */
public class ValueLocation extends BaseLocation {
        private final IScalarSort parentSort;
        
        public ValueLocation(ScalarSort parentSort) {
                super(  new Name(parentSort.name() + "::" + "value"),
                        parentSort.getValueSort(),
                        new ArrayOfSort(parentSort)
                        );
                this.parentSort = parentSort;
        }
        
        /**
         * Returns the arithmetic type this function belongs to.
         * @return
         */
        public IScalarSort getScalarSort() {
                return parentSort;
        }
}
