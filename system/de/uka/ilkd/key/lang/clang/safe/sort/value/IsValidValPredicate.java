package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.lang.common.operator.BaseRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IPredicate;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rigid predicate <code>isValidVal : {parent}</code>.
 * @author oleg.myrk@gmail.com
 */
public class IsValidValPredicate extends BaseRigidOperator implements IPredicate {        
        private final ValueMarkerSort parent;
        
        public IsValidValPredicate(ValueMarkerSort parent) {
                super(  new Name("isValidVal"),
                        Sort.FORMULA,
                        new Sort[] { parent }
                        );
                this.parent = parent;
        }
        
        /**
         * Returns the value marker sort this function belongs to.
         * @return
         */
        public ValueMarkerSort getValueMarkerSort() {
                return parent;
        }
}
