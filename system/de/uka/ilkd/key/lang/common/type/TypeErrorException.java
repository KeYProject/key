package de.uka.ilkd.key.lang.common.type;

import de.uka.ilkd.key.lang.common.program.IProgramElement;

/**
 * An exception thrown in case of type error.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TypeErrorException extends RuntimeException {
        private final IProgramElement programElement;

        public TypeErrorException(String message, IProgramElement programElement) {
                super(message);
                this.programElement = programElement;
        }

        public IProgramElement getProgramElement() {
                return programElement;
        }
}
