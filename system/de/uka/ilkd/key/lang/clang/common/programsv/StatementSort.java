package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on statements.
 * 
 * @author oleg.myrk@gmail.com
 */
public class StatementSort extends BaseStatementProgramSVSort {

        public StatementSort() {
                super(new Name("ClangStatement"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                return pe instanceof IClangStatement;
        }        
}