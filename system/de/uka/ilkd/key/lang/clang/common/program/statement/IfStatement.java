package de.uka.ilkd.key.lang.clang.common.program.statement;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.util.ExtList;

public final class IfStatement extends BaseClangStatement {

        private final IClangExpression condition;

        private final Branch thenBranch;

        private final Branch elseBranch;

        public IfStatement(IClangExpression condition, Branch thenBranch,
                        Branch elseBranch) {
                super();
                this.condition = condition;
                this.thenBranch = thenBranch;
                this.elseBranch = elseBranch;
        }

        public IfStatement(ExtList children, IfStatement original) {
                super(children);
                this.condition = (IClangExpression) children.get(IClangExpression.class);
                Branch[] branches = (Branch[]) children.collect(Branch.class);
                this.thenBranch = branches[0];
                if (branches.length > 1)
                        this.elseBranch = branches[1];
                else
                        this.elseBranch = null;
        }
        
        public IProgramElement copy(ExtList children) {
                return new IfStatement(children, this);
        }
        
        public IClangExpression getCondition() {
                return condition;
        }

        public Branch getThenBranch() {
                return thenBranch;
        }

        public Branch getElseBranch() {
                return elseBranch;
        }

        public int getChildCount() {
                return elseBranch != null ? 3 : 2;
        }

        public IProgramElement getProgramElementAt(int i) {
                if (i == 0)
                        return condition;
                else if (i == 1)
                        return thenBranch;
                else if (i == 2 && elseBranch != null)
                        return elseBranch;
                else
                        throw new IndexOutOfBoundsException();
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchIfStatement(this);
        }
}
