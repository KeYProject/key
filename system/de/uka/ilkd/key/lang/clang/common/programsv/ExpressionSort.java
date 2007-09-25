package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on any expression.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ExpressionSort extends BaseExpressionProgramSVSort  {

        public ExpressionSort() {
                super(new Name("ClangExpression"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                return ClangExpressionUtil.isClangExpression(pe);
        }
}