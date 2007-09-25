package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.lang.clang.common.type.object.StructType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class ValueAssignment extends BaseClangExpression {
        public ValueAssignment(ExtList children, ValueAssignment original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new ValueAssignment(children, this);
        }
        
        public ValueAssignment(IClangExpression lhs, IClangExpression rhs) {
                super(lhs, rhs);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchValueAssignment(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                if (ClangExpressionUtil.isLvalue(getExpressionAt(0), environment) == Boolean.FALSE)
                        throw new TypeErrorException("Value assignment left-hand-side must be an lvalue", this);
                
                KeYJavaType typePairLHS = ClangExpressionUtil.getTypePair(
                                getExpressionAt(0), environment);
                KeYJavaType typePairRHS = ClangExpressionUtil.getTypePair(
                                getExpressionAt(1), environment);

                if (typePairLHS == null || typePairRHS == null)
                        return null;

                if (!(typePairLHS.getJavaType() == typePairRHS.getJavaType() && 
                      (typePairRHS.getJavaType() instanceof IClangValueType || 
                       typePairRHS.getJavaType() instanceof StructType)))
                        throw new TypeErrorException(
                                        "Value assignment applied to incompatible types (no implicit conversions)",
                                        this);

                return typePairLHS;
        }
}
