package de.uka.ilkd.key.lang.clang.common.programmeta;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.declaration.VariableDeclaration;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.statement.AllocateStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.lang.clang.common.program.statement.FrameBody;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.ArrayOfBaseProgramSV;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Program meta construct that replaces:
 * <pre>
 *      block-frame(#vars) {
 *              #otype #ovar;
 *              ...
 *      }
 * </pre>
 * with
 * <pre>
 *      block-frame(#vars, #ovar) {
 *              alocate #ovar;
 *              ...
 *      }
 * </pre>
 *           
 * @author oleg.myrk@gmail.com
 */
public class IntroduceBlockFrameVarDeclProgramMeta extends BaseClangProgramMeta implements IClangStatement {
        public IntroduceBlockFrameVarDeclProgramMeta(ArrayOfBaseProgramSV arguments) {
                super(buildName(), arguments);
        }

        public static Name buildName() {
                return new Name("#IntroduceBlockFrameVarDecl");
        }

        public IProgramElement execute(
                        IClangEnvironment context, SVInstantiations insts) {
                super.checkArgumentCount(1);
                
                Object inst = insts.getInstantiation(getArguments().getBaseProgramSV(0));
                if (!(inst != null && inst instanceof BlockFrame))
                        throw new RuntimeException("#IntroduceBlockFrameVarDecl should be applied schema variable instantiated with block frame");
                BlockFrame blockFrame = (BlockFrame)inst;
                
                if (!(blockFrame.getBody().getStatementCount() > 0 && blockFrame.getBody().getStatementAt(0) instanceof VariableDeclaration))
                                throw new RuntimeException("#IntroduceBlockFrameVarDecl should be applied schema variable instantiated with block frame containing local variable declaration");
                VariableDeclaration varDecl = (VariableDeclaration)blockFrame.getBody().getStatementAt(0);
                IClangVariable variable = varDecl.getVariable();
                
                int variableCount = blockFrame.getVariables().size(); 
                IClangVariable[] newVariables = new IClangVariable[ variableCount + 1 ];
                if (variableCount > 0)
                        blockFrame.getVariables().arraycopy(0, newVariables, 0, variableCount);
                newVariables[ variableCount ] = variable;
                
                int statementCount = blockFrame.getBody().getStatementCount();
                IClangStatement[] newStatements = new IClangStatement[statementCount];
                newStatements[0] = new AllocateStatement(variable);
                if (statementCount > 1)
                        blockFrame.getBody().getStatements().arraycopy(1, newStatements, 1, statementCount - 1);
                
                return new BlockFrame(new ArrayOfIClangVariable(newVariables), new FrameBody(new ArrayOfIClangStatement(newStatements)));
        }
}
