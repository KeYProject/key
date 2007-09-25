package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.util.ExtList;

public final class Comma extends BaseClangExpression {

        public Comma(ExtList children, Comma original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new Comma(children, this);
        }
        
        public Comma(IClangExpression lhs, IClangExpression rhs) {
                super(lhs, rhs);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchComma(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePairLHS = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                KeYJavaType typePairRHS = ClangExpressionUtil.getTypePair(getExpressionAt(1), environment);
                                
                if (typePairLHS == null || typePairRHS == null)
                        return null;
                
                return typePairRHS;
        }
}
