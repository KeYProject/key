package de.uka.ilkd.key.lang.clang.common.programmeta;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.lang.clang.common.program.statement.CompoundStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.FrameBody;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.ArrayOfBaseProgramSV;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;

/**
 * Program meta construct that replaces:
 * 
 * <pre>
 *         {
 *                 ...
 *         }
 * </pre>
 * 
 * with
 * 
 * <pre>
 *         block-frame() {
 *                 ...
 *         }
 * </pre>
 * 
 * @author oleg.myrk@gmail.com
 */
public final class EnterBlockFrameProgramMeta extends BaseClangProgramMeta implements
                IClangStatement {
        public EnterBlockFrameProgramMeta(ArrayOfBaseProgramSV arguments) {
                super(buildName(), arguments);
        }
                
        public static Name buildName() {
                return new Name("#EnterBlockFrame");
        }

        public IProgramElement execute(IClangEnvironment context,
                        SVInstantiations insts) {
                super.checkArgumentCount(1);

                Object inst = insts.getInstantiation(getArguments()
                                .getBaseProgramSV(0));
                if (!(inst != null && inst instanceof CompoundStatement))
                        throw new RuntimeException(
                                        "#EnterBlockFrame should be applied schema variable instantiated with compound statement");
                CompoundStatement compoundStatement = (CompoundStatement) inst;

                return new BlockFrame(
                                new ArrayOfIClangVariable(),
                                new FrameBody(compoundStatement.getStatements()));
        }
}
