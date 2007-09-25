package de.uka.ilkd.key.lang.common.program;

import java.io.IOException;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.pprinter.ProgramPrinterUtil;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * Base implementation of a program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseProgramElement extends DummyProgramElement implements
                IProgramElement {
        public BaseProgramElement() {
        }

        public BaseProgramElement(ExtList children) {
        }

        /**
         * This constructor is used to create new AST node by modifying the
         * children of the old one. Every AST node of type T that can be copied
         * should have such constructor with the second parameter having type T.
         * 
         * @param children
         *                children to use
         * @param original
         *                the original AST node providing additional features
         *                (if needed)
         */
        public BaseProgramElement(ExtList children, BaseProgramElement original) {
        }

        /**
         * Computes the hash code as the hash code of the runtime class.
         */
        public int hashCode() {
                int result = 17;
                result = 37 * result + this.getClass().hashCode();
                return result;
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
         * @inheritDocs
         */
        public abstract boolean equalsModRenaming(
                        IProgramElement programElement, NameAbstractionTable nat);

        /**
         * Provides a default implementation of program printer.
         * 
         * @return
         */
        public abstract IProgramPrinter createDefaultPrinter();

        /**
         * @inheritDocs
         */
        public boolean equals(Object o) {
                if (o == this)
                        return true;
                if (!(o instanceof IProgramElement))
                        return false;

                return equalsModRenaming((IProgramElement) o,
                                NameAbstractionTableDisabled.INSTANCE);
        }

        /**
         * A disabled name abstraction table where program elements are
         * equivalent only when the are equal.
         */
        static class NameAbstractionTableDisabled extends NameAbstractionTable {

                public static final NameAbstractionTableDisabled INSTANCE = new NameAbstractionTableDisabled();

                public void add(SourceElement pe1, SourceElement pe2) {
                }

                public boolean sameAbstractName(SourceElement pe1,
                                SourceElement pe2) {
                        return pe1.equals(pe2);
                }
        }

        /**
         * Default implementation of matching that reduces to object equality.
         * 
         * @param source
         * @param matchCond
         * @return
         */
        public MatchConditions match(SourceData source,
                        MatchConditions matchCond) {
                final ProgramElement src = source.getSource();
                Debug.out("Program match start (template, source)", this, src);

                if (!this.equals(src)) {
                        Debug
                                        .out(
                                                        "Program match failed. Incompatible AST nodes (template, source)",
                                                        this, src);
                        return null;
                }
                source.next();
                return matchCond;
        }
}