package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

public class PredicateCollector extends Visitor {

private HashMap<Operator, ArrayList<Sort>> predicates = new HashMap<Operator, ArrayList<Sort>>();
        
        private Services services;
        
        public PredicateCollector(Services services) {
                this.services = services;
        }
        
        @Override
        public void visit(Term visited) {
                if (isPredicate(visited, this.services)) {
                        addPredicate(visited);
                }
        }
        
        public HashMap<Operator, ArrayList<Sort>> getFoundPredicates() {
                return predicates;
        }
        
        private void addPredicate(Term t) {
                if (predicates.containsKey(t.op())) {
                        this.updatePredicate(t);
                } else {
                        ArrayList<Sort> sorts = new ArrayList<Sort>();
                        for (int i = 0; i < t.arity(); i++) {
                                sorts.add(t.sub(i).sort());
                        }
                        predicates.put(t.op(), sorts);
                }
        }
        
        private void updatePredicate(Term t) {
                ArrayList<Sort> sorts = predicates.get(t.op());
                //update the sorts of the arguments
                for (int i = 0; i < t.arity(); i++) {
                        Sort supersort = getSuperSort(t.sub(i).sort(), sorts.get(i));
                        sorts.set(i, supersort);
                }
        }
        
        private Sort getSuperSort(Sort s1, Sort s2) {
                if (s1.extendsTrans(s2)) {
                        return s2;
                } else if (s2.extendsTrans(s1)) {
                        return s1;
                }
                //TODO add Debug message
                return null;
        }
        
        private boolean isPredicate (Term t, Services services) {
                boolean isPred = false;
                if (t.op() instanceof Function &&
                                t.sort() == Sort.FORMULA) {
                        isPred = true;
                }
                
                
                
                return isPred;
        }

}
