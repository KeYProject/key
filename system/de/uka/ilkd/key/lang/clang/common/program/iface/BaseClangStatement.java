package de.uka.ilkd.key.lang.clang.common.program.iface;

import java.util.Set;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.clang.common.walker.VariableCollector;
import de.uka.ilkd.key.util.ExtList;

public abstract class BaseClangStatement extends BaseClangNonTerminalProgramElement implements IClangStatement {
        public BaseClangStatement() {
                super();
        }
        
        public BaseClangStatement(ExtList children) {
                super(children);
        }
        
        public BaseClangStatement(ExtList children, BaseClangStatement original) {
                super(children, original);
        }
}
