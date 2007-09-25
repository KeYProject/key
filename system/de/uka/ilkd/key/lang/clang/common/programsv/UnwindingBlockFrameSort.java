package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on block frame with no statements but more than zero
 * variables to unwind.
 * 
 * @author oleg.myrk@gmail.com
 */
public class UnwindingBlockFrameSort extends BaseStatementProgramSVSort {

        public UnwindingBlockFrameSort() {
                super(new Name("ClangUnwindingBlockFrame"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (!(pe instanceof BlockFrame))
                        return false;
                BlockFrame blockFrame = (BlockFrame)pe;
                
                if (blockFrame.getBody().getStatementCount() != 0)
                        return false;
                
                if (blockFrame.getVariables().size() == 0)
                        return false;
                        
                return true;
       }
}