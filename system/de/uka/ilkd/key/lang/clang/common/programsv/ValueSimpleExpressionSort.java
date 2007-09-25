package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.literal.IntegerLiteral;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on simple expression of value type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ValueSimpleExpressionSort extends BaseExpressionProgramSVSort implements IVariableSort {

        public ValueSimpleExpressionSort() {
                super(new Name("ClangValueSimpleExpression"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (pe instanceof IClangVariable) {
                        IClangVariable variable = (IClangVariable) pe;
                        return variable.getTypePair().getJavaType() instanceof IClangValueType;
                }
                if (pe instanceof IntegerLiteral)
                        return true;
                return false;
        }
}