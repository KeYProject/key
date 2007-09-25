package de.uka.ilkd.key.lang.clang.common.program.statement;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.util.ExtList;

public final class DestroyStatement extends BaseClangStatement {

        private final IClangExpression expression;

        public DestroyStatement(ExtList children, DestroyStatement original) {
                super(children);
                this.expression = (IClangExpression) children.get(IClangExpression.class);
        }
        
        public IProgramElement copy(ExtList children) {
                return new DestroyStatement(children, this);
        }
        
        public DestroyStatement(IClangExpression expression) {
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
                p.dispatchDestroyStatement(this);
        }
}
