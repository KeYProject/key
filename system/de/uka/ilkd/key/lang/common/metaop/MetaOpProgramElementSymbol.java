package de.uka.ilkd.key.lang.common.metaop;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.logic.sort.NullSortImpl;

/**
 * This class is useful in order to temporarily encapsulate a program
 * element into a term. It should be immediately processed by a logic
 * meta operation.
 * 
 * @author oleg.myrk@gmail.com
 */
public class MetaOpProgramElementSymbol extends TermSymbol {
        final IProgramElement contents;

        public MetaOpProgramElementSymbol(IProgramElement contents) {
                super(new Name("#MetaOpProgramElement"), NullSortImpl.NULL);
                this.contents = contents;
        }

        /**
         * Returns the contained program element.
         * 
         * @return
         */
        public IProgramElement getContents() {
                return contents;
        }

        /**
         * @inhertiDocs
         */
        public int arity() {
                return 0;
        }
}
