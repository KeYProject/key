package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.Location;

/**
 * A program variable. Program variables have a name, a type pair (a type
 * and a sort), and are a typed terminal program element and a logic location.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IVariable extends ITypedProgramElement, ITerminalProgramElement, Named, Location {
        public KeYJavaType getTypePair();
}
