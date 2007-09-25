package de.uka.ilkd.key.lang.clang.common.program.statement;

import java.lang.Exception;

import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.util.ExtList;

public final class CompoundStatement extends BaseClangStatement {

        private final ArrayOfIClangStatement statements;

        public CompoundStatement(ArrayOfIClangStatement statements) {
                this.statements = statements;
        }

        public CompoundStatement(ExtList children, CompoundStatement original) {
                super(children);
                statements = new ArrayOfIClangStatement((IClangStatement[]) children
                                .collect(IClangStatement.class));
        }
        
        public IProgramElement copy(ExtList children) {
                return new CompoundStatement(children, this);
        }
        
        public int getChildCount() {
                return statements.size();
        }

        public IProgramElement getProgramElementAt(int index) {
                return statements.getIClangStatement(index);
        }
        
        public ArrayOfIClangStatement getStatements() {
                return statements;
        }

        public int getStatementCount() {
                return statements.size();
        }

        public IClangStatement getStatementAt(int index) {
                return statements.getIClangStatement(index);
        }

        public void dispatch(IClangProgramDispatcher w) throws Exception {
                w.dispatchCompoundStatement(this);
        }        
}
