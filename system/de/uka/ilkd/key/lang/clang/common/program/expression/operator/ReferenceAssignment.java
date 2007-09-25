package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.util.ExtList;

public final class ReferenceAssignment extends BaseClangExpression {
        
        public ReferenceAssignment(ExtList children, ReferenceAssignment original) {
                super(children, original);
        }        
        
        public IProgramElement copy(ExtList children) {
                return new ReferenceAssignment(children, this);
        }
        
        public ReferenceAssignment(IClangExpression lhs, IClangExpression rhs) {
                super(lhs, rhs);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchReferenceAssignment(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.TRUE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                if (!(getExpressionAt(0) instanceof IProgramVariable))
                        throw new TypeErrorException("Reference assignment left-hand-side must be applied an object variable", this);                        
                
                KeYJavaType typePairLHS = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                KeYJavaType typePairRHS = ClangExpressionUtil.getTypePair(getExpressionAt(1), environment);
                
                if (typePairLHS == null || typePairRHS == null)
                        return null;
                
                if (!(typePairLHS.getJavaType() == typePairRHS.getJavaType() &&
                      typePairLHS.getJavaType() instanceof IClangObjectType))
                    throw new TypeErrorException("Reference assignment applied to incompatible types", this);
                
                return typePairRHS;
        }
}
