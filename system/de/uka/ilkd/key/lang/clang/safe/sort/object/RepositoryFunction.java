package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.common.operator.BaseRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rigid repository function <code>{parent}::&lt;lookup&gt; : int -> {parent}</code>.
 * @author oleg.myrk@gmail.com
 */
public class RepositoryFunction extends BaseRigidOperator implements IFunction {
        private final IInstantiableObjectSort parent;
                
        /**
         * Creates the repository function.
         * @param parent
         * @param intSort
         */
        public RepositoryFunction(InstantiableObjectSort parent, Sort intSort) {
                super(  new Name(parent.name() + "::<lookup>"),
                        parent,
                        new Sort[]{ intSort }
                        );
                this.parent = parent;
        }
        
        /**
         * Returns the sort this function belongs to.
         * @return
         */                
        public IInstantiableObjectSort getInstantiableObjectSort() {
                return parent;
        }
}
