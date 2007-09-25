package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.IVoidSort;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;

/**
 * CDL void sort.
 * @author oleg.myrk@gmail.com
 */
public class VoidSort extends BaseObjectSort implements IVoidSort {

        /**
         * Creates void sort.
         * @param objectMarkerSort
         */
        public VoidSort(ObjectMarkerSort objectMarkerSort) {
                super(  formatName(), 
                        SetAsListOfSort.EMPTY_SET
                                .add(objectMarkerSort));
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
         * @return
         */
        public static Name formatName() {
                return new Name("Void");
        }
}
