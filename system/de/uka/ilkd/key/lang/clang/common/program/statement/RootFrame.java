package de.uka.ilkd.key.lang.clang.common.program.statement;

import java.lang.Exception;
import java.util.Set;

import de.uka.ilkd.key.lang.common.match.IKeyedMatchPatternProgramElement;
import de.uka.ilkd.key.lang.common.match.IKeyedMatchSourceProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.util.PatternUtil;
import de.uka.ilkd.key.util.ExtList;

public final class RootFrame extends BaseClangStatement implements IKeyedMatchPatternProgramElement, IKeyedMatchSourceProgramElement {

        private final FrameBody body;

        public RootFrame(FrameBody body) {
                this.body = body;
        }

        public RootFrame(ExtList children, RootFrame original) {
                super(children);
                body = (FrameBody) children.get(FrameBody.class);
        }
        
        public IProgramElement copy(ExtList children) {
                return new RootFrame(children, this);
        }
        
        public FrameBody getBody() {
                return body;
        }

        public int getChildCount() {
                return 1;
        }

        public IProgramElement getProgramElementAt(int index) {
                if (index == 0)
                        return body;
                else
                        throw new ArrayIndexOutOfBoundsException();
        }

        public void dispatch(IClangProgramDispatcher w) throws Exception {
                w.dispatchRootFrame(this);
        }
        
        public void addMatchSourceKeys(Set set) {
                set.add(PatternUtil.SCHEMA_VARIABLE_KEY);
                set.add(PatternUtil.buildKey(this));
                body.addMatchSourceKeys(set);
        }

        public void addMatchPatternKeys(Set set) {
                if (body.getStatementCount() > 0) {
                        IClangStatement statement = body.getStatementAt(0);
                        if (statement instanceof IKeyedMatchPatternProgramElement)
                                ((IKeyedMatchPatternProgramElement)statement).addMatchPatternKeys(set);
                        else
                                set.add(PatternUtil.buildKey(statement));
                }
                else
                        set.add(PatternUtil.buildKey(this));
        }
}
