package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;

/**
 * CDL value marker sort.
 * @author oleg.myrk@gmail.com
 */
public class ValueMarkerSort extends BaseValueSort {
        
        /**
         * Predicate <code>isValidVal</code> associated with this type instance.
         */
        private IsValidValPredicate isValidValPredicate;
        
        /**
         * Creates value marker sort.
         */
        public ValueMarkerSort() {
                super(formatName(), SetAsListOfSort.EMPTY_SET);
        }
        
        /**
         * Returns predicate <code>isValidVal</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public IsValidValPredicate getIsValidValPredicate() {
                return isValidValPredicate;
        }
        
        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder builder) {
                super.register(builder);                
                this.isValidValPredicate = new IsValidValPredicate(this);
                builder.getFunctionNS().add(isValidValPredicate);
        }
        
        /**
         * Formats sort's name.
         * @param id
         * @return
         */
        public static Name formatName() {
                return new Name("Value");
        }        
}
