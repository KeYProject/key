package de.uka.ilkd.key.lang.clang.common.programmeta;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.lang.clang.common.program.statement.DestroyStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.FrameBody;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.ArrayOfBaseProgramSV;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Program meta construct that replaces:
 * <pre>
 *      block-frame(#var1, ..., #varn) {
 *      }
 * </pre>
 * with
 * <pre>
 *      block-frame() {
 *              destroy #var1;
 *              ...
 *              destroy #varn;
 *      }
 * </pre>
 *           
 * @author oleg.myrk@gmail.com
 */
public class UnwindBlockFrameProgramMeta extends BaseClangProgramMeta implements IClangStatement {
        public UnwindBlockFrameProgramMeta(ArrayOfBaseProgramSV arguments) {
                super(buildName(), arguments);
        }

        public static Name buildName() {
                return new Name("#UnwindBlockFrame");
        }

        public IProgramElement execute(
                        IClangEnvironment context, SVInstantiations insts) {
                super.checkArgumentCount(1);
                
                Object inst = insts.getInstantiation(getArguments().getBaseProgramSV(0));
                if (!(inst != null && inst instanceof BlockFrame))
                        throw new RuntimeException("#UnwindBlockFrame should be applied schema variable instantiated with block frame");
                BlockFrame blockFrame = (BlockFrame)inst;

                if (!(blockFrame.getBody().getStatementCount() == 0))
                        throw new RuntimeException("#UnwindBlockFrame should be applied schema variable instantiated with block frame without statements");
                
                if (!(blockFrame.getVariables().size() > 0))
                        throw new RuntimeException("#UnwindBlockFrame should be applied schema variable instantiated with block frame with at least one variable to unwind");
                
                int variableCount = blockFrame.getVariables().size();
                IClangStatement[] newStatements = new IClangStatement[variableCount];
                for(int i = 0; i < blockFrame.getVariables().size(); i++) {
                        IClangVariable variable = blockFrame.getVariables().getIClangVariable(i);                
                        newStatements[i] = new DestroyStatement(variable);
                }
                return new BlockFrame(new ArrayOfIClangVariable(), new FrameBody(new ArrayOfIClangStatement(newStatements)));
        }
}
