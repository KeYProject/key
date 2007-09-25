package de.uka.ilkd.key.lang.common.sort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.SetOfSort;

/**
 * Base class of primitive types. Primitive sorts are equal iff their
 * names are equal. 
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BasePrimitiveSort extends PrimitiveSort implements ISort {
        /**
         * Creates primitive sort with given name.
         * @param name
         * @param extendsSorts
         */
        public BasePrimitiveSort(Name name) {
                super(name);
        }

        /**
         * Returns the sorts this sort extends.
         * @return the sorts this sort extends
         */
        public abstract SetOfSort extendsSorts();
        
        /**
         * @inheritDocs
         */
        public final boolean equals(Object o) {
                if (o instanceof BasePrimitiveSort)
                        return this.name().equals(((BasePrimitiveSort)o).name());
                else
                        return false;
        }
        
        /**
         * @inheritDocs
         */
        public final int hashCode() {
                return this.name().hashCode();
        }
}
