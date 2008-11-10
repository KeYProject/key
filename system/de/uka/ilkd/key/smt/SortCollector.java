package de.uka.ilkd.key.smt;

import java.util.HashSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.sort.Sort;

public class SortCollector extends Visitor {

        private HashSet<Sort> sorts = new HashSet<Sort>();
        
        @Override
        public void visit(Term visited) {
                if ( !sorts.contains(visited.sort()) ) {
                        sorts.add(visited.sort());
                }
        }
        
        public HashSet<Sort> getFoundSorts() {
                return this.sorts;
        }

}
