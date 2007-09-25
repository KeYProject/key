package de.uka.ilkd.key.lang.clang.common.programsv;


import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.literal.IntegerLiteral;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on integer literals.
 * @author oleg.myrk@gmail.com
 */
public class IntegerLiteralSort extends BaseExpressionProgramSVSort {

        public IntegerLiteralSort() {
            super(new Name("ClangIntegerLiteral"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
            return (pe instanceof IntegerLiteral);
        }
}
