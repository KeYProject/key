package de.uka.ilkd.key.lang.clang.common.program.iface;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;

/**
 * Represents C type references.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IClangTypeReference extends IClangProgramElement {
        KeYJavaType getTypePair();
}
