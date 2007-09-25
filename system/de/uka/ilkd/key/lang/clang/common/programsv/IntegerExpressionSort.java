package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.type.declaration.IntegerTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.value.ArithmeticType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on expressions of integer value types.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntegerExpressionSort extends BaseExpressionProgramSVSort {

        public IntegerExpressionSort() {
                super(new Name("ClangIntegerExpression"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (ClangExpressionUtil.isClangExpression(pe)) {
                        Type type = ClangExpressionUtil.getTypePair(pe, context).getJavaType();
                        if (type instanceof ArithmeticType)
                                return ((ArithmeticType)type).getDecl() instanceof IntegerTypeDecl;
                }
                return false;
        }
}