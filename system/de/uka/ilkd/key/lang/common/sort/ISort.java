package de.uka.ilkd.key.lang.common.sort;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.sort.SetOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Represents a logic sort.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface ISort extends Sort, Named {
        /**
         *  Returns a set of direct predecessors in the sort hierarchy.
         *  @return
         */
        SetOfSort extendsSorts();


        /**
         * Returns true iff the given sort is a transitive supersort of this sort
         * or it is the same.
         * @param sort
         * @return
         */
        boolean extendsTrans(Sort sort);
}
