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

public class Negative extends BaseClangExpression {
        public Negative(IClangExpression expression) {
                super(expression);
        }

        public Negative(ExtList children, Negative original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new Negative(children, this);
        }
        
        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchNegative(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePair = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                if (typePair == null)
                        return null;
                
                if (!(ArithmeticUtils.isNonPromotableType(typePair.getJavaType())))
                        throw new TypeErrorException("Negative applied to incompatible type (no promotions)", this);
        
                return typePair;
        }
}
