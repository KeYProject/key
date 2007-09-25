package de.uka.ilkd.key.lang.clang.common.program.iface;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.program.BaseVariable;
import de.uka.ilkd.key.logic.Name;

/**
 * Base C program variable.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseClangVariable extends BaseVariable implements
                IClangVariable {
        public BaseClangVariable(Name name, KeYJavaType t) {
                super(name, t);
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                return this.getTypePair();
        }

        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }

        public IProgramPrinter createDefaultPrinter() {
                return new ClangProgramPrinter();
        }                

        public Set getAllVariables() {
                Set result = new HashSet();
                result.add(this);
                return result;
        }        
}
