package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.util.ExtList;

/**
 * Base implementation of a terminal program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseTerminalProgramElement extends BaseProgramElement
                implements ITerminalProgramElement
                 {

        public BaseTerminalProgramElement() {
                super();
        }

        public BaseTerminalProgramElement(ExtList children) {
                super(children);
        }

        public BaseTerminalProgramElement(ExtList children,
                        BaseTerminalProgramElement original) {
                super(children, original);
        }
        
        /**
         * Default implementation that only checks equality of runtime classes.
         * @param se
         * @param nat
         * @return
         */
        public boolean equalsModRenaming(IProgramElement pe,
                        NameAbstractionTable nat) {
                return (this.getClass() == pe.getClass());
        }        
}
