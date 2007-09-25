package de.uka.ilkd.key.lang.clang.common.program.iface;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.common.program.ITerminalProgramElement;
import de.uka.ilkd.key.logic.Name;

public interface IClangMemberReference extends ITerminalProgramElement, IClangProgramElement {
        Name getMemberName();
        KeYJavaType getMemberTypePair();
        KeYJavaType getContainerTypePair();        
}
