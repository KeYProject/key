package de.uka.ilkd.key.lang.clang.common.program.expression.operator.logic;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArithmeticUtils;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Or extends BaseClangExpression {
        private final KeYJavaType resultTypePair;

        public Or(IClangExpression lhs, IClangExpression rhs, KeYJavaType resultTypePair) {
                super(lhs, rhs);
                this.resultTypePair = resultTypePair;
        }

        public Or(ExtList children, Or original) {
                super(children, original);
                this.resultTypePair = original.resultTypePair;
        }
        
        public IProgramElement copy(ExtList children) {
                return new Or(children, this);
        }
        
        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchOr(this);
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
                     ArithmeticUtils.isNonPromotableIntegerType(typePair0.getJavaType()))
                        throw new TypeErrorException("Or applied to incompatible types (no promotions)", this);
                
                return resultTypePair;
        }
}
