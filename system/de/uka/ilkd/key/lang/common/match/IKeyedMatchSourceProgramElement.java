package de.uka.ilkd.key.lang.common.match;

import java.util.Set;

import de.uka.ilkd.key.lang.common.program.IProgramElement;

/**
 * A program element that can be a source in the program matching
 * mechanism. The keys built by this interface must contain at least one key
 * built by {@link IKeyedMatchPatternProgramElement#addMatchPatternKeys(Set)}
 * for all potentially applicable pattern program elements.
 * 
 * Terminology: pattern program elements can contain schema program elements and
 * are matched against source program element.
 * 
 * @see IKeyedMatchSourceProgramElement
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IKeyedMatchSourceProgramElement extends IProgramElement {
        /**
         * Builds the set of keys used to look up potentially applicable
         * patterns.
         * 
         * @see IKeyedMatchPatternProgramElement
         * @return
         */
        void addMatchSourceKeys(Set set);
}
