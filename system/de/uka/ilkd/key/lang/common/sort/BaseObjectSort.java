package de.uka.ilkd.key.lang.common.sort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.AbstractNonCollectionSort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.SetOfSort;

/**
 * Base class of object sorts. Object sorts are equal iff their
 * names are equal. Object sorts are distinct from primitive sorts
 * only because Null sort extends all object sorts.
 * 
 * TODO: get rid of hard-wired Null sort and have one BaseSort.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseObjectSort extends AbstractNonCollectionSort implements ObjectSort, ISort {
        /**
         * Creates object sort with given name.
         * @param name
         */
        public BaseObjectSort(Name name) {
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
                if (o instanceof ObjectSort)
                        return this.name().equals(((ObjectSort)o).name());
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
