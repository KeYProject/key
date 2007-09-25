package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangMemberReference;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.logic.Name;

public class MemberReferenceProgramSV extends BaseClangProgramSV implements IClangMemberReference {
        public MemberReferenceProgramSV(Name name, BaseProgramSVSort s) {
                super(name, s);
        }
        public Name getMemberName() {
                throw new IllegalStateException("MemberReferenceProgramSV does not have a member name");
        }
        
        public KeYJavaType getMemberTypePair() {
                throw new IllegalStateException("MemberReferenceProgramSV does not have a member type");
        }
        
        public KeYJavaType getContainerTypePair() {
                throw new IllegalStateException("MemberReferenceProgramSV does not have a container type!"); 
        }
        
}
