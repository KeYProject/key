package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.lang.clang.common.sort.value.IArithmeticSort;
import de.uka.ilkd.key.lang.clang.safe.sort.SortUtil;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;

/**
 * CDL arithmetic sort.
 * @author oleg.myrk@gmail.com
 */
public class ArithmeticSort extends BaseValueSort implements IArithmeticSort {
        /**
         * Arithemtic type id. 
         */
        private final String id;
                
        /**
         * Creates arithmetic sort with given name.
         * @param id
         * @parma valueMarkerSort
         */
        public ArithmeticSort(String id, ValueMarkerSort valueMarkerSort) {
                super(  formatName(id), 
                        SetAsListOfSort.EMPTY_SET
                                .add(valueMarkerSort));
                this.id = id;
        }
        
        /**
         * Returns arithmetic type id.
         * @return
         */
        public String getId() {
                return id;
        }
        
        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder sortBuilder) {
                super.register(sortBuilder);
        }
        
        /**
         * Formats sort's name.
         * @param id
         * @return
         */        
        public static Name formatName(String id) {
                return new Name(SortUtil.escapeCIdentifier(id));
        }
}
