package de.uka.ilkd.key.lang.common.program;

import java.util.Set;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.rule.MatchConditions;

/**
 * Represents a program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IProgramElement extends ProgramElement {

        /**
         * @see {@link Object#equals()}
         * @return
         */
        boolean equals(Object o);

        /**
         * @see {@link Object#hashCode()}
         * @return
         */
        int hashCode();

        /**
         * @see {@link Object#toString()}
         * @return
         */
        String toString();

        /**
         * This method returns true if two program parts are equal modulo
         * renaming. The equality is mainly a syntactical equality with some
         * exceptions: if a variable is declared we abstract from the name of
         * the variable, so the first declared variable gets e.g. the name
         * decl_1, the second declared decl_2 and so on.
         */
        boolean equalsModRenaming(IProgramElement programElement,
                        NameAbstractionTable nat);

        /**
         * Matches the source {@link SourceData#getSource()} against the pattern
         * represented by this object. In case of a successful match the
         * resulting {@link MatchConditions} with the found instantiations of
         * the schema variables is returned. If the match failed, <tt>null</tt>
         * is returned instead.
         * 
         * @param source
         *                the SourceData with the program element to match
         * @param matchCond
         *                the MatchConditions found up to this point
         * @return the resulting match conditions or <tt>null</tt> if the
         *         match failed
         */
        MatchConditions match(SourceData source, MatchConditions matchCond);

        /**
         * Returns a set of program variables (subclasses of {@link IVariable})
         * present in this program element.
         * 
         * @return
         */
        Set getAllVariables();

        /**
         * Provides a default implementation of program printer.
         * 
         * @return
         */
        IProgramPrinter createDefaultPrinter();
}
