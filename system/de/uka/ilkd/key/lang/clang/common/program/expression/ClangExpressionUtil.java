package de.uka.ilkd.key.lang.clang.common.program.expression;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;

/**
 * C expression utilities. C expression either implements
 * {@link IClangExpression}, or {@link BaseProgramSV}.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ClangExpressionUtil {
        
        /**
         * Tests if program element is a valid C expression;
         * @param programElement
         * @return
         */
        public static boolean isClangExpression(IProgramElement programElement) {
                return programElement instanceof IClangExpression;
        }
        
        /**
         * Computes whether the C expression is an lvalue.
         * @param expression
         * @param environment
         * @return the type or <code>null</code> if the type is not known yet
         * @throws TypeErrorException
         */
        public static KeYJavaType getTypePair(IProgramElement expression, IClangEnvironment environment) {
                if (expression instanceof BaseProgramSV)
                        return null;
                else if (expression instanceof IClangExpression)
                        return ((IClangExpression)expression).getTypePair(environment);
                else
                        throw new TypeErrorException("Not a C expression or program schema variable", expression);
        }

        /**
         * Computes the type of C expression.
         * @param expression
         * @param environment
         * @return lvalue status or <code>null</code> if the type is not known yet
         * @throws TypeErrorException
         */
        public static Boolean isLvalue(IProgramElement expression, IClangEnvironment environment) {
                if (expression instanceof BaseProgramSV)
                        return null;
                else if (expression instanceof IClangExpression)
                        return ((IClangExpression)expression).isLvalue(environment);
                else
                        throw new TypeErrorException("Not a C expression or program schema variable", expression);
        }       
}
