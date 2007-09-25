package de.uka.ilkd.key.lang.clang.common.program.statement;

import java.lang.Exception;
import java.util.Set;

import de.uka.ilkd.key.lang.common.match.IKeyedMatchPatternProgramElement;
import de.uka.ilkd.key.lang.common.match.IKeyedMatchSourceProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.util.PatternUtil;
import de.uka.ilkd.key.util.ExtList;

public class BlockFrame extends BaseClangStatement implements IKeyedMatchPatternProgramElement,
                IKeyedMatchSourceProgramElement {

        private final ArrayOfIClangVariable variables;

        private final FrameBody body;

        public BlockFrame(ArrayOfIClangVariable variables, FrameBody body) {
                this.variables = variables;
                this.body = body;
        }

        public BlockFrame(ExtList children, BlockFrame original) {
                super(children);
                variables = new ArrayOfIClangVariable(
                                (IClangVariable[]) children
                                                .collect(IClangVariable.class));
                body = (FrameBody) children.get(FrameBody.class);
        }
        
        public IProgramElement copy(ExtList children) {
                return new BlockFrame(children, this);
        }

        public ArrayOfIClangVariable getVariables() {
                return variables;
        }

        public FrameBody getBody() {
                return body;
        }

        public int getChildCount() {
                return variables.size() + 1;
        }

        public IProgramElement getProgramElementAt(int index) {
                if (index < variables.size())
                        return variables.getIClangVariable(index);
                index -= variables.size();
                if (index == 0)
                        return body;
                else
                        throw new ArrayIndexOutOfBoundsException();
        }

        public void dispatch(IClangProgramDispatcher w) throws Exception {
                w.dispatchBlockFrame(this);
        }

        public void addMatchSourceKeys(Set set) {
                body.addMatchSourceKeys(set);
                set.add(PatternUtil.buildKey(this));
        }

        public void addMatchPatternKeys(Set set) {
                if (body.getStatementCount() > 0) {
                        IClangStatement statement = body.getStatementAt(0);
                        if (statement instanceof IKeyedMatchPatternProgramElement)
                                ((IKeyedMatchPatternProgramElement) statement)
                                                .addMatchPatternKeys(set);
                        else
                                set.add(PatternUtil.buildKey(statement));
                } else
                        set.add(PatternUtil.buildKey(this));
        }
}
