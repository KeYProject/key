package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.annotation.Annotation;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * An implementation of legacy methods of a program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class DummyProgramElement implements IProgramElement {

        /**
         * @deprecated
         */
        public final boolean equalsModRenaming(SourceElement se,
                        NameAbstractionTable nat) {
                if (!(se instanceof IProgramElement)) return false;
                return equalsModRenaming((IProgramElement)se, nat);
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
        public final SourceElement getFirstElement() {
                return this;
        }

        /**
         * @deprecated
         */
        public final SourceElement getLastElement() {
                return this;
        }

        /**
         * @deprecated
         */
        public Position getStartPosition() {
                return PositionInfo.UNDEFINED.getStartPosition();
        }

        /**
         * @deprecated
         */
        public Position getEndPosition() {
                return PositionInfo.UNDEFINED.getEndPosition();
        }

        /**
         * @deprecated
         */
        public Position getRelativePosition() {
                return PositionInfo.UNDEFINED.getRelativePosition();
        }

        /**
         * @deprecated
         */
        public PositionInfo getPositionInfo() {
                return PositionInfo.UNDEFINED;
        }

        /**
         * @deprecated
         */
        public Comment[] getComments() {
                return new Comment[0];
        }

        /**
         * @deprecated
         */
        public Annotation[] getAnnotations() {
                return new Annotation[0];
        }

        /**
         * @deprecated
         */
        public int getAnnotationCount() {
                return 0;
        }
}