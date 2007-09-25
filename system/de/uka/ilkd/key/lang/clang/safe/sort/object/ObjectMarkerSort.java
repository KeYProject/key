package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;

/**
 * CDL object marker sort.
 * @author oleg.myrk@gmail.com
 */
public class ObjectMarkerSort extends BaseObjectSort {
        
        /**
         * Predicate <code>isValidPtr</code> associated with this type instance.
         */
        private IsValidPtrPredicate isValidPtrPredicate;
        
        /**
         * Predicate <code>objExists</code> associated with this type instance.
         */
        private ObjExistsPredicate objExistsPredicate;
        
        /**
         * Creates object marker sort.
         */
        public ObjectMarkerSort() {
                super(formatName(), SetAsListOfSort.EMPTY_SET);
        }
        
        /**
         * Returns predicate <code>isValidPtr</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public IsValidPtrPredicate getIsValidPtrPredicate() {
                return isValidPtrPredicate;
        }
        
        /**
         * Returns predicate <code>objExists</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public ObjExistsPredicate getObjExistsPredicate() {
                return objExistsPredicate;
        }
        
        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder sortBuilder) {
                super.register(sortBuilder);
                this.isValidPtrPredicate = new IsValidPtrPredicate(this);
                sortBuilder.getFunctionNS().add(isValidPtrPredicate);
                this.objExistsPredicate = new ObjExistsPredicate(this);
                sortBuilder.getFunctionNS().add(objExistsPredicate);                
        }
        
        /**
         * Formats sort's name.
         * @param id
         * @return
         */
        public static Name formatName() {
                return new Name("Object");
        }        
}
