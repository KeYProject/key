package de.uka.ilkd.key.lang.clang.common.program.type;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangTerminalProgramElement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.common.program.IProgramElement;

/**
 * Type reference.
 * @author oleg.myrk@gmail.com
 */
public class TypeReference extends BaseClangTerminalProgramElement implements IClangTypeReference {
        KeYJavaType typePair;
        
        public TypeReference(KeYJavaType typePair) {
                this.typePair = typePair;
        }

        public KeYJavaType getTypePair() {
                return typePair;
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchTypeReference(this);
        }        
        
        public boolean equalsModRenaming(IProgramElement pe,
                        NameAbstractionTable nat) {
                if (this.getClass() != pe.getClass()) {
                        return false;
                }
                final IClangTypeReference ref = (IClangTypeReference) pe;
                return ref.getTypePair().equals(typePair);
        }
}
