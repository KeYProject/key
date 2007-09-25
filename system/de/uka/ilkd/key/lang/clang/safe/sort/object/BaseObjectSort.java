package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.safe.sort.ClangObjectSort;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetOfSort;

/**
 * Base CDL object sort implementation.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseObjectSort extends ClangObjectSort {
        /**
         * Creates base object sort.
         * @param name
         * @param extendsSorts
         */
        public BaseObjectSort(Name name, SetOfSort extendsSorts) {
                super(name, extendsSorts);
        }

        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder sortBuilder) {
                this.addDefinedSymbols(sortBuilder.getFunctionNS(), sortBuilder.getSortNS());
        } 
}
