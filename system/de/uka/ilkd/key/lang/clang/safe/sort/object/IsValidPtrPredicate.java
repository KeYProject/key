package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.common.operator.BaseNonRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IPredicate;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Non-rigid predicate <code>isValidPtr : {parent}</code>.
 * @author oleg.myrk@gmail.com
 */
public class IsValidPtrPredicate extends BaseNonRigidOperator implements IPredicate {
        private final ObjectMarkerSort parent;
        
        public IsValidPtrPredicate(ObjectMarkerSort parent) {
                super(  new Name("isValidPtr"),
                        Sort.FORMULA,
                        new Sort[]{ parent }
                        );
                this.parent = parent;
        }
        
        /**
         * Returns the sort this function belongs to.
         * @return
         */                
        public ObjectMarkerSort getObjectMarkerSort() {
                return parent;
        }        
}