package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.logic.Name;

public class ExpressionProgramSV extends BaseClangProgramSV implements IClangExpression {
        public ExpressionProgramSV(Name name, BaseProgramSVSort s) {
                super(name, s);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                throw new IllegalStateException("ExpressionProgramSV does not have an Lvalue property!");
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                throw new IllegalStateException("ExpressionProgramSV does not have a type!");
        }       
}
