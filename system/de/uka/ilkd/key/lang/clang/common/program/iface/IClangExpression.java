package de.uka.ilkd.key.lang.clang.common.program.iface;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.program.ITypedProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;

/**
 * Represents an expression in C.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IClangExpression extends ITypedProgramElement, IProgramElement, IClangProgramElement {
        /**
         * Tells if the expression is an l-value.
         * 
         * @param environment
         * @return the a boolean or <code>null</code> if it is not known yet.
         */
        Boolean isLvalue(IClangEnvironment environment);

        /**
         * Computes the type pair based on given environment information.
         * 
         * @return the type pair or <code>null</code> if the type is not known
         *         yet.
         * @throws TypeErrorException
         */
        KeYJavaType getTypePair(IClangEnvironment environment)
                        throws TypeErrorException;
}
