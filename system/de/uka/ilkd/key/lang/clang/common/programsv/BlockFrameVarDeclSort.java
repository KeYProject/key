package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.declaration.VariableDeclaration;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on block frame with outstanding automatic object variable 
 * declaration without an inintializer.
 * 
 * @author oleg.myrk@gmail.com
 */
public class BlockFrameVarDeclSort extends BaseStatementProgramSVSort  {

        public BlockFrameVarDeclSort() {
                super(new Name("ClangBlockFrameVarDecl"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (!(pe instanceof BlockFrame))
                        return false;
                BlockFrame blockFrame = (BlockFrame)pe;
                
                if (blockFrame.getBody().getStatementCount() == 0)
                        return false;
                IClangStatement statement = blockFrame.getBody().getStatementAt(0);
                
                if (!(statement instanceof VariableDeclaration))
                        return false;
                VariableDeclaration varDecl = (VariableDeclaration)statement;
                
                if (varDecl.getIsStatic())
                        return false;
                if (varDecl.getInitializer() != null)
                        return false;
                
                KeYJavaType typePair = varDecl.getTypeReference().getTypePair();
                if (typePair.getJavaType() instanceof IClangValueType)
                        return false;
                
                return true;
        }
}