package de.uka.ilkd.key.lang.clang.common.program.statement;

import java.util.Set;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.lang.common.match.IKeyedMatchPatternProgramElement;
import de.uka.ilkd.key.lang.common.match.IKeyedMatchSourceProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.util.PatternUtil;
import de.uka.ilkd.key.util.ExtList;

public final class ExpressionStatement extends BaseClangStatement implements IKeyedMatchPatternProgramElement, IKeyedMatchSourceProgramElement {

        private final IClangExpression expression;

        public ExpressionStatement(ExtList children, ExpressionStatement original) {
                super(children);
                this.expression = (IClangExpression) children.get(IClangExpression.class);
        }
        
        public IProgramElement copy(ExtList children) {
                return new ExpressionStatement(children, this);
        }
        
        public ExpressionStatement(IClangExpression expression) {
                this.expression = expression;
        }

        public IClangExpression getExpression() {
                return expression;
        }
        
        public int getChildCount() {
                return 1;
        }

        public IProgramElement getProgramElementAt(int i) {
                if (i == 0)
                        return expression;
                else
                        throw new IndexOutOfBoundsException();
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchExpressionStatement(this);
        }

        public void addMatchSourceKeys(Set set) {
                set.add(PatternUtil.buildKey(expression));
        }
        
        public void addMatchPatternKeys(Set set) {
                set.add(PatternUtil.buildKey(expression));
        }        
}
