package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangMemberReference;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class MemberAccess extends BaseClangExpression {
        private final IClangMemberReference memberReference;
        
        public MemberAccess(IClangExpression expression, IClangMemberReference member) {
                super(expression);
                this.memberReference = member;
        }
        
        public MemberAccess(ExtList children, MemberAccess original) {
                super(children, original);
                this.memberReference = original.memberReference;
        }
        
        public IProgramElement copy(ExtList children) {
                return new MemberAccess(children, this);
        }
        
        public int getChildCount() {
                return 2;
        }
        
        public IProgramElement getProgramElementAt(int index) {
                if (index == 0) 
                        return getExpressionAt(0);
                else if (index == 1)
                        return memberReference;
                else
                        throw new ArrayIndexOutOfBoundsException();
        }
        
        public IClangExpression getExpression() {
                return getExpressionAt(0);
        }
        
        public IClangMemberReference getMemberReference() {
                return memberReference;
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchMemberAccess(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return ClangExpressionUtil.isLvalue(getExpression(), environment);
        }

        public KeYJavaType getTypePair(IClangEnvironment environment) {
                IClangExpression expression = getExpression();
                IClangMemberReference memberReference = getMemberReference();
                                
                KeYJavaType expressionTypePair = ClangExpressionUtil.getTypePair(expression, environment);
                if (expressionTypePair == null)
                        return null;

                if (memberReference instanceof BaseProgramSV)
                        return null;
                
                KeYJavaType memberTypePair = memberReference.getMemberTypePair();
                KeYJavaType memberContainerTypePair = memberReference.getContainerTypePair();
                
                if (expressionTypePair.getJavaType() != memberContainerTypePair.getJavaType())
                        throw new TypeErrorException(
                                "Member access applied to incompatible type",
                                this);
                
                return memberTypePair;
        }
}
