package de.uka.ilkd.key.lang.clang.common.program.statement;

import java.lang.Exception;
import java.util.Set;

import de.uka.ilkd.key.lang.common.match.IKeyedMatchSourceProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangNonTerminalProgramElement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.util.PatternUtil;
import de.uka.ilkd.key.util.ExtList;

public final class FrameBody extends BaseClangNonTerminalProgramElement implements
                IKeyedMatchSourceProgramElement {

        private final ArrayOfIClangStatement statements;

        public FrameBody(ArrayOfIClangStatement statements) {
                this.statements = statements;
        }

        public FrameBody(ExtList children, FrameBody original) {
                super(children);
                statements = new ArrayOfIClangStatement((IClangStatement[]) children
                                .collect(IClangStatement.class));
        }
        
        public IProgramElement copy(ExtList children) {
                return new FrameBody(children, this);
        }
        
        public int getChildCount() {
                return statements.size();
        }

        public IProgramElement getProgramElementAt(int index) {
                return statements.getIClangStatement(index);
        }

        public int getStatementCount() {
                return statements.size();
        }

        public IClangStatement getStatementAt(int index) {
                return statements.getIClangStatement(index);
        }

        public ArrayOfIClangStatement getStatements() {
                return statements;
        }

        public void dispatch(IClangProgramDispatcher w) throws Exception {
                w.dispatchFrameBody(this);
        }

        public void addMatchSourceKeys(Set set) {
                if (getStatementCount() > 0) {
                        IClangStatement firstChild = getStatementAt(0);
                        if (firstChild instanceof IKeyedMatchSourceProgramElement)
                                ((IKeyedMatchSourceProgramElement) firstChild)
                                                .addMatchSourceKeys(set);
                        else
                                set.add(PatternUtil.buildKey(firstChild));
                }
        }
}
