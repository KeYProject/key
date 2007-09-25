package de.uka.ilkd.key.lang.clang.common.program.iface;

import java.util.Set;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangServices;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.clang.common.walker.VariableCollector;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.program.BaseTypedNonTerminalProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.util.ExtList;

/**
 * Base implementation of C expressions.
 */
public abstract class BaseClangExpression extends
                BaseTypedNonTerminalProgramElement implements IClangExpression {

        private final ArrayOfIClangExpression children;

        public BaseClangExpression() 
        {
                this(new IClangExpression[0]);
        }
        
        public BaseClangExpression(IClangExpression lhs, IClangExpression rhs) {
                this(new IClangExpression[] { lhs, rhs });
        }

        public BaseClangExpression(IClangExpression unaryChild) {
                this(new IClangExpression[] { unaryChild });
        }

        public BaseClangExpression(IClangExpression[] children) {
                this(new ArrayOfIClangExpression(children));
        }
        
        public BaseClangExpression(ArrayOfIClangExpression children) {
                this.children = children;
        }

        public BaseClangExpression(ExtList children, BaseClangExpression original) {
                super(children, original);
                this.children = new ArrayOfIClangExpression(
                                (IClangExpression[]) children
                                                .collect(IClangExpression.class));
        }

        public int getChildCount() {
                return children.size();
        }

        public IProgramElement getProgramElementAt(int index) {
                return children.getIClangExpression(index);
        }

        public final int getExpressionCount() {
                return children.size();
        }
        
        public final IClangExpression getExpressionAt(int index) {
                return children.getIClangExpression(index);
        }
        
        public final ArrayOfIClangExpression getExpressions() {
                return children;
        }

        public KeYJavaType getTypePair(ILangServices services,
                        Namespace sortNS, Namespace symbolNS) {
                return getTypePair(((IClangServices) services).getEnvironment(
                                sortNS, symbolNS));
        }

        public IProgramPrinter createDefaultPrinter() {
                return new ClangProgramPrinter();
        }                

        public Set getAllVariables() {
                VariableCollector collector = new VariableCollector(this);
                collector.start();
                return collector.result();
        }        
}
