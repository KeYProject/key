package de.uka.ilkd.key.lang.common.operator;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.NonRigidFunctionLocation;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Base implementation of a location function.
 * 
 * @author oleg.myrk@gmail.com
 */
public class BaseLocation extends NonRigidFunctionLocation implements IFunction {
        public BaseLocation(Name name, Sort sort, ArrayOfSort argSorts) {
                super(name, sort, argSorts);
        }
}
