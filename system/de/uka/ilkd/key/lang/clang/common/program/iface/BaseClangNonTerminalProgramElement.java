package de.uka.ilkd.key.lang.clang.common.program.iface;

import java.util.Set;

import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.clang.common.walker.VariableCollector;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.program.BaseNonTerminalProgramElement;
import de.uka.ilkd.key.util.ExtList;

public abstract class BaseClangNonTerminalProgramElement extends BaseNonTerminalProgramElement implements IClangProgramElement {
        public BaseClangNonTerminalProgramElement() {
                super();
        }
        
        public BaseClangNonTerminalProgramElement(ExtList children) {
                super(children);
        }

        public BaseClangNonTerminalProgramElement(ExtList children, BaseClangNonTerminalProgramElement original) {
                super(children, original);
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
