package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangTerminalProgramElement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangMemberReference;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.logic.Name;

/**
 * Structured type member.
 * @author oleg.myrk@gmail.com
 */
public class MemberReference extends BaseClangTerminalProgramElement implements IClangMemberReference {
        Name name;
        KeYJavaType typePair;
        KeYJavaType containerTypePair;
        
        public MemberReference(Name name, KeYJavaType typePair, KeYJavaType containerTypePair) {
                this.name = name;
                this.typePair = typePair;
                this.containerTypePair = containerTypePair;
        }

        public Name getMemberName() {
                return name;
        }
        
        public KeYJavaType getMemberTypePair() {
                return typePair;
        }
        
        public KeYJavaType getContainerTypePair() {
                return containerTypePair;
        }        

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchMemberReference(this);
        }        
        
        public boolean equalsModRenaming(IProgramElement pe,
                        NameAbstractionTable nat) {
                if (this.getClass() != pe.getClass()) {
                        return false;
                }
                final IClangMemberReference ref = (IClangMemberReference) pe;
                return ref.getMemberName().equals(name) && ref.getContainerTypePair().equals(containerTypePair);
        }
}
