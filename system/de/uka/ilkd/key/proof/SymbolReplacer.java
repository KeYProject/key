package de.uka.ilkd.key.proof;

import java.util.Map;

import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;

public class SymbolReplacer extends ProgVarReplacer {

    public SymbolReplacer(Map m) {
        super(m);       
    }

    /**
     * replaces in a term
     */
    public Term replace(Term t) {
        if (t.op() instanceof RigidFunction && map.containsKey(t.op())) {
            return replaceRigidFunction(t);
        } else {
            return super.replace(t);
        }
    }

    private Term replaceRigidFunction(Term t) {
        assert t.op() instanceof RigidFunction;
        assert t.javaBlock().isEmpty();

        RigidFunction rf = (RigidFunction) map.get(t.op());
        
        if (rf != t.op()) {
            final Term newSubTerms[] = new Term[t.arity()];
            final ArrayOfQuantifiableVariable[] boundVars =
                new ArrayOfQuantifiableVariable [t.arity ()];
            
            for(int i = 0, ar = t.arity(); i < ar; i++) {
                newSubTerms[i] = replace(t.sub(i));
                boundVars[i] = t.varsBoundHere(i);
            }
            
            return TermFactory.DEFAULT.createTerm(rf,
                    newSubTerms,
                    boundVars,
                    JavaBlock.EMPTY_JAVABLOCK);

        } else {
            return standardReplace(t);
        }
    }
    
}
