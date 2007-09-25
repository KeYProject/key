package de.uka.ilkd.key.lang.common.operator;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Base implementation of a non-rigid operator.
 * 
 * @author oleg.myrk@gmail.com
 */
public class BaseNonRigidOperator extends NonRigidFunction {
        public BaseNonRigidOperator(Name name, Sort sort, Sort[] argSorts) {
                super(name, sort, argSorts);
        }
}
