package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ReferenceAssignment;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ValueAssignment;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on expressions that do not have an 
 * assignment (value or reference) at the top level and are of value type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ValueNonAssignmentExpressionSort extends BaseExpressionProgramSVSort {

        public ValueNonAssignmentExpressionSort() {
                super(new Name("ClangValueNonAssignmentExpression"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                return 
                ClangExpressionUtil.isClangExpression(pe) &&
                ClangExpressionUtil.getTypePair(pe, context).getJavaType() instanceof IClangValueType &&
                !(pe instanceof ValueAssignment || pe instanceof ReferenceAssignment);
        }
}