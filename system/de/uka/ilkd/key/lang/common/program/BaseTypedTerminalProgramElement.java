package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.util.ExtList;

/**
 * Base implementation of typed terminal program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseTypedTerminalProgramElement extends
                BaseTerminalProgramElement implements ITypedProgramElement {
        public BaseTypedTerminalProgramElement() {
                super();
        }

        public BaseTypedTerminalProgramElement(ExtList children) {
                super(children);
        }

        public BaseTypedTerminalProgramElement(ExtList children,
                        BaseTypedTerminalProgramElement original) {
                super(children, original);
        }
}
