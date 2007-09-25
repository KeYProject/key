package de.uka.ilkd.key.lang.clang.safe.sort;

import de.uka.ilkd.key.lang.clang.common.sort.IClangValueSort;
import de.uka.ilkd.key.lang.common.sort.BasePrimitiveSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetOfSort;

/**
 * Base class of CDL value types. Value sorts are equal iff their
 * names are equal. 
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class ClangValueSort extends BasePrimitiveSort implements IClangValueSort {
        /**
         * Set of sorts this sort extends.
         */
        final SetOfSort extendsSorts;
        
        /**
         * Creates value sort with given name.
         * @param name
         * @param extendsSorts
         */
        protected ClangValueSort(Name name, SetOfSort extendsSorts) {
                super(name);
                this.extendsSorts = extendsSorts; 
                
        }
        /**
         * Returns the sorts this sort extends.
         * @return the sorts this sort extends
         */
        public SetOfSort extendsSorts() {
            return extendsSorts;
        }
}
