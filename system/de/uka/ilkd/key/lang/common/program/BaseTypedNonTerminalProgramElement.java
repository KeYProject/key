package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.util.ExtList;

/**
 * Base implementation of typed non-terminal program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseTypedNonTerminalProgramElement extends BaseNonTerminalProgramElement implements ITypedProgramElement {

        public BaseTypedNonTerminalProgramElement() {
                super();
        }

        public BaseTypedNonTerminalProgramElement(ExtList children) {
                super(children);
        }

        public BaseTypedNonTerminalProgramElement(ExtList children,
                        BaseNonTerminalProgramElement original) {
                super(children, original);
        }
}
