package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.literal.IntegerLiteral;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on complex expressions.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ComplexExpressionSort extends BaseExpressionProgramSVSort {

        public ComplexExpressionSort() {
                super(new Name("ClangComplexExpression"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                return ClangExpressionUtil.isClangExpression(pe) && 
                        !(pe instanceof IClangVariable) &&
                        !(pe instanceof IntegerLiteral);
        }
}