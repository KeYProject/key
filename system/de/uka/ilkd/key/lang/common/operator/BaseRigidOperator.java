package de.uka.ilkd.key.lang.common.operator;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Base implementation of a rigid operator.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseRigidOperator extends RigidFunction implements IOperator {
        public BaseRigidOperator(Name name, Sort sort, Sort[] argSorts) {
                super(name, sort, argSorts);
        }
}
