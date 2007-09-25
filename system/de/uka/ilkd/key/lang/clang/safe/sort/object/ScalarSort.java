package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * CDL scalar sort.
 * @author oleg.myrk@gmail.com
 */
public class ScalarSort extends InstantiableObjectSort implements IScalarSort {
        /**
         * Scalar type's value sort (can be both value and object).
         */
        private final Sort valueSort;
        
        /**
         * Location <code>value</code> associated with this type instance.
         */
        private ValueLocation valueLocation;
        
        /**
         * Creates scalar sort with given value sort (can be both value and object).
         * @param valueSort
         * @param objectMarkerSort
         * @param voidSort
         */
        public ScalarSort(Sort valueSort, ObjectMarkerSort objectMarkerSort, VoidSort voidSort) {
                super(  formatName(valueSort), 
                        SetAsListOfSort.EMPTY_SET
                                .add(objectMarkerSort)
                                .add(voidSort));
                this.valueSort = valueSort;
        }
        
        /**
         * Returns scalar sort's value sort.
         * @return
         */
        public Sort getValueSort() {
                return valueSort;
        }
        
        /**
         * Returns location <code>value</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SymbolInfo)} is called.
         * @return
         */
        public ValueLocation getValueLocation() {
                return valueLocation;
        }

        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder sortBuilder) {
                super.register(sortBuilder);
                this.valueLocation = new ValueLocation(this);
                sortBuilder.getFunctionNS().add(valueLocation);
        }
        
        /**
         * Formats sort's name.
         * @param valueSort
         * @return
         */
        public static Name formatName(Sort valueSort) {
                return new Name(valueSort.name() + "@");
        }
}
