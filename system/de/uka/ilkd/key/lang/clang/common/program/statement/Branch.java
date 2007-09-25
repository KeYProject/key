package de.uka.ilkd.key.lang.clang.common.program.statement;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangNonTerminalProgramElement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.util.ExtList;

public final class Branch extends BaseClangNonTerminalProgramElement implements IClangStatement {

        private final IClangStatement body;
 
        public Branch(IClangStatement body){
                super();
                this.body = body;
        }

        public Branch(ExtList children, Branch original) {
                super(children);
                this.body = (IClangStatement)children.get(IClangStatement.class);
        }
        
        public IProgramElement copy(ExtList children) {
                return new Branch(children, this);
        }
        
        public IClangStatement getBody() {
                return body;
        }        
        
        public int getChildCount() {
                return 1;
        }

        public IProgramElement getProgramElementAt(int i) {
                if (i == 0)
                        return body;
                throw new IndexOutOfBoundsException();
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchBranch(this);
        }        
}
