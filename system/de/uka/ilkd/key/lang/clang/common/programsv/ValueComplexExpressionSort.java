package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.literal.IntegerLiteral;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on complex expressions of value type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ValueComplexExpressionSort extends BaseExpressionProgramSVSort{

        public ValueComplexExpressionSort() {
                super(new Name("ClangValueComplexExpression"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                return ClangExpressionUtil.isClangExpression(pe) && 
                       !(pe instanceof IClangVariable) &&
                       !(pe instanceof IntegerLiteral) &&
                       ClangExpressionUtil.getTypePair(pe, context).getJavaType() instanceof IClangValueType;
        }
}