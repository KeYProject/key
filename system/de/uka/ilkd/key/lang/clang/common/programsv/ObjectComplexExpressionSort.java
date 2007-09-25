package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on complex expressions of object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ObjectComplexExpressionSort extends BaseExpressionProgramSVSort {

        public ObjectComplexExpressionSort() {
                super(new Name("ClangObjectComplexExpression"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                return ClangExpressionUtil.isClangExpression(pe) && 
                       !(pe instanceof IClangVariable) &&
                       ClangExpressionUtil.getTypePair(pe, context).getJavaType() instanceof IClangObjectType;
        }
}