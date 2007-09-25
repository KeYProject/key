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

public final class Not extends BaseClangExpression {
        private final KeYJavaType resultTypePair;

        public Not(IClangExpression child, KeYJavaType resultTypePair) {
                super(child);
                this.resultTypePair = resultTypePair;
        }

        public Not(ExtList children, Not original) {
                super(children, original);
                this.resultTypePair = original.resultTypePair;
        }
        
        public IProgramElement copy(ExtList children) {
                return new Not(children, this);
        }
        
        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchNot(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePair = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                
                if (typePair == null)
                        return null;
                
                if (!ArithmeticUtils.isNonPromotableIntegerType(typePair.getJavaType()))
                        throw new TypeErrorException("Not applied to incompatible types (no promotions)", this);
                
                return resultTypePair;
        }
}
