package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.statement.CompoundStatement;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on compound statements.
 * 
 * @author oleg.myrk@gmail.com
 */
public class NonEmptyCompoundStatementSort extends BaseStatementProgramSVSort {

        public NonEmptyCompoundStatementSort() {
                super(new Name("ClangNonEmptyCompoundStatement"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (!(pe instanceof CompoundStatement))
                        return false;
                CompoundStatement compoundStatement = (CompoundStatement)pe;
                
                if (compoundStatement.getStatementCount() == 0)
                        return false;
                return true;
        }
}