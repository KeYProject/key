package de.uka.ilkd.key.lang.common.match;

import java.util.Set;

import de.uka.ilkd.key.lang.common.program.IProgramElement;

/**
 * A program element that can work as a pattern in the program matching mechanism.
 * 
 * Terminology: pattern program elements can contain schema program elements
 * and are matched against source program element.
 *  
 * @see IKeyedMatchSourceProgramElement
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IKeyedMatchPatternProgramElement extends IProgramElement {
        /**
         * Builds the set of keys for this program element acting as a pattern.
         * @see IKeyedMatchSourceProgramElement
         * @param set
         */
        void addMatchPatternKeys(Set set);
}
