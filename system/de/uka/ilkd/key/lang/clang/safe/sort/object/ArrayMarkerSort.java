package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;

/**
 * CDL array marker sort.
 * @author oleg.myrk@gmail.com
 */
public class ArrayMarkerSort extends BaseObjectSort {
        /**
         * Object marker sort.
         */
        private final ObjectMarkerSort objectMarkerSort;
        
        /**
         * Function <code>size</code> associated with this type instance.
         */
        private SizeFunction sizeFunction;
        
        /**
         * Creates array marker sort.
         */
        public ArrayMarkerSort(ObjectMarkerSort objectMarkerSort) {
                super(formatName(), SetAsListOfSort.EMPTY_SET.add(objectMarkerSort));
                this.objectMarkerSort = objectMarkerSort;
        }
        
        /**
         * Returns array sort's object marker sort.
         * @return
         */
        public ObjectMarkerSort getObjectMarkerSort() {
                return objectMarkerSort;
        }
        
        /**
         * Returns function <code>size</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public SizeFunction getSizeFunction() {
                return sizeFunction;
        }
        
        /**
         * Registers associated symbols.
         * @param sortBuilder
         */
        public void register(SortBuilder sortBuilder) {
                super.register(sortBuilder);
                this.sizeFunction = new SizeFunction(this, sortBuilder.getIntSort());
                sortBuilder.getFunctionNS().add(sizeFunction);                
        }
        
        
        /**
         * Formats sort's name.
         * @param id
         * @return
         */
        public static Name formatName() {
                return new Name("Array");
        }        
}
