package de.uka.ilkd.key.lang.clang.safe.sort;

import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.value.IPointerSort;
import de.uka.ilkd.key.lang.common.sort.BaseObjectSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetOfSort;

/**
 * Base class of CDL object sorts. Object sorts are equal iff their
 * names are equal.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class ClangObjectSort extends BaseObjectSort implements IClangObjectSort, IPointerSort {
        /**
         * Set of sorts this sort extends.
         */
        final SetOfSort extendsSorts;
        
        /**
         * Creates object sort with given name and set of sorts it extends.
         * @param name
         * @param extendsSorts
         */
        public ClangObjectSort(Name name, SetOfSort extendsSorts) {
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
        
        /**
         * Returns pointer sort's target sort.
         * @return
         */
        public IClangObjectSort getTargetSort() {
                return this;
        }
}
