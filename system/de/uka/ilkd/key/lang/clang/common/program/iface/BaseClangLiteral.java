package de.uka.ilkd.key.lang.clang.common.program.iface;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.iface.IClangServices;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.program.BaseTypedTerminalProgramElement;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Namespace;

public abstract class BaseClangLiteral extends BaseTypedTerminalProgramElement implements IClangExpression {

        public BaseClangLiteral() {
                super();
        }
        
        public KeYJavaType getTypePair(ILangServices services, Namespace sortNS, Namespace symbolNS) {
                return getTypePair(((IClangServices)services).getEnvironment(sortNS, symbolNS));
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public IProgramPrinter createDefaultPrinter() {
                return new ClangProgramPrinter();
        }
                
        public Set getAllVariables() {
                return new HashSet();                
        }
}
