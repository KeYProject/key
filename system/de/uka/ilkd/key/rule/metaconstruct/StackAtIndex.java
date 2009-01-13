package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class StackAtIndex extends AbstractMetaOperator {

    public StackAtIndex() {
        super(new Name("#stackAtIndex"), 1);
    }

    /** calculates the resulting term. 
     */
    public Term calculate(Term term, SVInstantiations svInst, 
                          Services services) {  
    
        ObjectSort s = (ObjectSort) services.getJavaInfo().getKeYJavaType("javax.realtime.MemoryStack").getSort();     
        
        Function repos
            = (Function) ((SortDefiningSymbols) s).lookupSymbol(AbstractSort.OBJECT_REPOSITORY_NAME);
        
         
        return termFactory.createFunctionTerm(repos, term.sub(0));
    }

    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }

    public Sort sort() {        
        return METASORT;
    }
    
}
