package de.uka.ilkd.key.lang.clang.common.program.statement;

import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.util.ExtList;

public final class WhileStatement extends BaseClangStatement {

        private final IClangExpression condition;

        private final Branch body;

        public WhileStatement(IClangExpression condition, Branch body) {
                super();
                this.condition = condition;
                this.body = body;
        }

        public WhileStatement(ExtList children, WhileStatement original) {
                super(children);
                this.condition = (IClangExpression) children.get(IClangExpression.class);
                this.body = (Branch) children.get(Branch.class);
        }
        
        public IProgramElement copy(ExtList children) {
                return new WhileStatement(children, this);
        }
        
        public IClangExpression getCondition() {
                return condition;
        }

        public Branch getBody() {
                return body;
        }

        public int getChildCount() {
                return 2;
        }

        public IProgramElement getProgramElementAt(int i) {
                if (i == 0)
                        return condition;
                else if (i == 1)
                        return body;
                else
                        throw new IndexOutOfBoundsException();
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchWhileStatement(this);
        }
}
