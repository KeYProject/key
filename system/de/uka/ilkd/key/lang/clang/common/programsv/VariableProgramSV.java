package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.logic.Name;

public class VariableProgramSV extends ExpressionProgramSV implements IClangVariable {
        public VariableProgramSV(Name name, BaseProgramSVSort s) {
                super(name, s);
        }
        
        public KeYJavaType getTypePair() {
                throw new IllegalStateException("VariableProgramSV does not have a type property!");
        }
}
