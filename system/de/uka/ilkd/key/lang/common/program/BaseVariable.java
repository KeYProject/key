package de.uka.ilkd.key.lang.common.program;

import java.io.IOException;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.lang.common.pprinter.ProgramPrinterUtil;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.Debug;

/**
 * Base implementation of program variables.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseVariable extends LocationVariable implements
                IVariable, ITerminalProgramElement {
        
        public BaseVariable(Name name, KeYJavaType t) {
                super(new ProgramElementName(name.toString()), t);
        }

        /**
         * Two variables are considered to be equal if they are assigned to the
         * same abstract name or if they are the same object.
         */
        public boolean equalsModRenaming(IProgramElement se,
                        NameAbstractionTable nat) {
                return nat.sameAbstractName(this, se);
        }

        /**
         * @inheritDocs
         */
        public final Name name() {
                return super.name();
        }

        /**
         * @inheritDocs
         */
        public final KeYJavaType getTypePair(ILangServices services,
                        Namespace sortNS, Namespace symbolNS) {
                return getKeYJavaType();
        }

        /**
         * @inheritDocs
         */
        public final KeYJavaType getTypePair() {
                return getKeYJavaType();
        }

        /**
         * @inheritDocs
         */
        public final String toString() {
                try {
                        return ProgramPrinterUtil
                                        .formatProgramElementNoLF(this);
                } catch (IOException e) {
                        String message = this.getClass()
                                        + ".toString() failed: " + e;
                        Debug.fail(message);
                        Debug.out(e);
                        return "<" + e + ">";
                }
        }

        /**
         * @deprecated
         */
        public final KeYJavaType getKeYJavaType(Services services,
                        ExecutionContext e) {
                return getKeYJavaType();
        }
        
        /**
         * @deprecated
         */
        public final void visit(Visitor v) {
                throw new IllegalStateException("Using Visitor is unsupported!");
        }

        /**
         * @deprecated
         */
        public final void prettyPrint(PrettyPrinter p)
                        throws java.io.IOException {
                throw new IllegalStateException(
                                "Using PrettyPrinter is unsupported!");
        }

        /**
         * @deprecated
         */
        public final boolean equalsModRenaming(SourceElement se,
                        NameAbstractionTable nat) {
                if (!(se instanceof IProgramElement)) return false;
                return equalsModRenaming((IProgramElement)se, nat);
        }
        
}