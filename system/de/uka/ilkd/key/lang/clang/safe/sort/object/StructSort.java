package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.safe.sort.SortUtil;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;

/**
 * CDL struct sort.
 * @author oleg.myrk@gmail.com
 */
public class StructSort extends StructuredSort {
        
        /**
         * Creates struct sort.
         * @param id struct identifier
         */
        public StructSort(String id, ObjectMarkerSort objectMarkerSort, VoidSort voidSort) {
                super(id, formatName(id), objectMarkerSort, voidSort);
        }
        
        /**
         * Formats sort's name.
         * @param id
         * @return
         */
        public static Name formatName(String id) {
                return new Name("$" + SortUtil.escapeCIdentifier(id));
        }        
}
