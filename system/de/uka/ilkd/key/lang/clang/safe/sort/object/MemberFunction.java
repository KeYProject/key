package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.IStructuredSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.MemberInfo;
import de.uka.ilkd.key.lang.common.operator.BaseRigidOperator;
import de.uka.ilkd.key.lang.common.operator.IFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rigid member accessor function <code>{parent.name}::{id} : {sort}</code>.
 * @author oleg.myrk@gmail.com
 */
public class MemberFunction extends BaseRigidOperator implements IFunction {
        private final IStructuredSort parent;
        private final MemberInfo memberInfo;
                
        public MemberFunction(StructuredSort parent, MemberInfo memberInfo) {
                super(  new Name(parent.name() + "::" + memberInfo.getId()),
                        memberInfo.getSort(),
                        new Sort[]{ parent }
                        );
                this.parent = parent;
                this.memberInfo = memberInfo;
        }
        
        /**
         * Returns the structured sort this function belongs to.
         * @return
         */                
        public IStructuredSort getStructuredSort() {
                return parent;
        }
        
        /**
         * Returns member info of this member accessor function.
         * @return
         */
        public MemberInfo getMemberInfo() {
                return memberInfo;
        }
}
