package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.java.ProgramElement;

/**
 * An implementation of legacy methods of non terminal program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class DummyNonTerminalProgramElement extends DummyProgramElement implements INonTerminalProgramElement {
        public ProgramElement getChildAt(int index) {
                return getProgramElementAt(index);
        }
}
