package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on expressions of pointer value types.
 * 
 * @author oleg.myrk@gmail.com
 */
public class PointerExpressionSort extends BaseExpressionProgramSVSort {

        public PointerExpressionSort() {
                super(new Name("ClangPointerExpression"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                return ClangExpressionUtil.isClangExpression(pe) && 
                ClangExpressionUtil.getTypePair(pe, context).getJavaType() instanceof PointerType;
        }
}