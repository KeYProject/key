package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import java.lang.Exception;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.util.ExtList;

public final class Parentheses extends BaseClangExpression {

        public Parentheses(ExtList children, Parentheses original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new Parentheses(children, this);
        }
        
        public Parentheses(IClangExpression child) {
                super(child);
        }

        public void dispatch(IClangProgramDispatcher w) throws Exception {
                w.dispatchParentheses(this);
        }

        public Boolean isLvalue(IClangEnvironment environment) {
                return ClangExpressionUtil
                                .isLvalue(getExpressionAt(0), environment);
        }

        public KeYJavaType getTypePair(IClangEnvironment environment) {
                return ClangExpressionUtil.getTypePair(getExpressionAt(0),
                                environment);
        }
}
