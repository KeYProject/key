package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.lang.clang.safe.sort.ClangValueSort;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetOfSort;

/**
 * CDL value sort base implementation.
 * @author oleg.myrk@gmail.com
 */
public class BaseValueSort extends ClangValueSort {
        /**
         * Creates base value sort.
         * @param name
         * @parma extendsSorts
         */
        public BaseValueSort(Name name, SetOfSort extendsSorts) {
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
