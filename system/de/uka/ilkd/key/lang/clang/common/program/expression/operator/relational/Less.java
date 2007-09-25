package de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArithmeticUtils;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Less extends BaseClangExpression {
        private final KeYJavaType resultTypePair;

        public Less(IClangExpression lhs, IClangExpression rhs, KeYJavaType resultTypePair) {
                super(lhs, rhs);
                this.resultTypePair = resultTypePair;
        }

        public Less(ExtList children, Less original) {
                super(children, original);
                this.resultTypePair = original.resultTypePair;
        }
        
        public IProgramElement copy(ExtList children) {
                return new Less(children, this);
        }
        
        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchLess(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePair0 = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                KeYJavaType typePair1 = ClangExpressionUtil.getTypePair(getExpressionAt(1), environment);
                
                if (typePair0 == null || typePair1 == null)
                        return null;
                
                if (!(typePair0.getJavaType() == typePair1.getJavaType()) &&
                     (ArithmeticUtils.isNonPromotableType(typePair0.getJavaType()) ||
                     typePair0.getJavaType() instanceof PointerType))
                        throw new TypeErrorException("Less comparison applied to incompatible types (no promotions)", this);
                
                return resultTypePair;
        }
}
