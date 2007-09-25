package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.logic.Namespace;

/**
 * Represents a program element that has a type pair (a type and a sort).
 * 
 * @author oleg.myrk@gmail.com
 */
public interface ITypedProgramElement extends IProgramElement {
        /**
         * Computes the type pair based on given environment information.
         * 
         * @param services
         * @param sortNS
         * @param symbolNS
         * @return the type pair or <code>null</code> if the type is not known yet
         * 
         * @throws TypeErrorException in case of type error
         */
        public KeYJavaType getTypePair(ILangServices services, Namespace sortNS, Namespace symbolNS) throws TypeErrorException;
}
