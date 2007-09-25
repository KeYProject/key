package de.uka.ilkd.key.lang.clang.common.program.iface;

import java.util.Set;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.clang.common.walker.VariableCollector;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.program.BaseTerminalProgramElement;
import de.uka.ilkd.key.util.ExtList;

public abstract class BaseClangTerminalProgramElement extends BaseTerminalProgramElement implements IClangProgramElement {
        public BaseClangTerminalProgramElement() {
                super();
        }
        
        
        public IProgramPrinter createDefaultPrinter() {
                return new ClangProgramPrinter();
        }                

        public final Set getAllVariables() {
                VariableCollector collector = new VariableCollector(this);
                collector.start();
                return collector.result();
        }        
}
