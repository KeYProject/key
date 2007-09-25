package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.logic.Name;

public class TypeProgramSV extends BaseClangProgramSV implements IClangTypeReference {
        public TypeProgramSV(Name name, BaseProgramSVSort s) {
                super(name, s);
        }
        
        public KeYJavaType getTypePair() {
                throw new IllegalStateException("TypeProgramSV does not have a type property!");
        }        
}
