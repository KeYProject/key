package de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArithmeticUtils;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Multiply extends BaseClangExpression {

        public Multiply(ExtList children, Multiply original) {
                super(children, original);
        }

        public Multiply(IClangExpression lhs, IClangExpression rhs) {
                super(lhs, rhs);
        }
        
        public IProgramElement copy(ExtList children) {
                return new Multiply(children, this);
        }
        
        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchMultiply(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePairLHS = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                KeYJavaType typePairRHS = ClangExpressionUtil.getTypePair(getExpressionAt(1), environment);
                                
                if (typePairLHS == null || typePairRHS == null)
                        return null;
                
                // if "arithm * arithm"
                if (typePairLHS.getJavaType() == typePairRHS.getJavaType() && ArithmeticUtils.isNonPromotableType(typePairLHS.getJavaType()) && ArithmeticUtils.isNonPromotableType(typePairRHS.getJavaType()))
                        return typePairLHS;
                else
                        throw new TypeErrorException("Multiply applied to incompatible types (no promotions)", this);
        }
}
