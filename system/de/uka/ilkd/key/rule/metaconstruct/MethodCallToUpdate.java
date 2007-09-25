package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.PosInProgram;

/**
 * Transforms a method call into an update. Used for strictly pure methods.
 * 
 * @author jseidel
 *
 */

public class MethodCallToUpdate extends AbstractMetaOperator {

    public MethodCallToUpdate() {
        super(new Name("#methodCallToUpdate"), 2);
    }
    
    public Term calculate( Term term, SVInstantiations svInst, Services services ) {
        
        System.out.println("MethodCallToUpdate.calculate() called.");
        System.out.println("term.sub(0) is of type " + term.sub(0).getClass().getName() + " " +
                        "and contains " + term.sub(0).toString() );
        System.out.println("term.sub(1) is of type " + term.sub(1).getClass().getName() + " " +
                        "and contains " + term.sub(1).toString() );
        //System.out.println("term.sub(2) is of type " + term.sub(2).getClass().getName() );
        
        
        // fish for the first method body statement
        
        ProgramElement pe = term.sub(0).javaBlock().program();

        while( pe != null && (pe instanceof ProgramPrefix) ) {
            ProgramPrefix pf = (ProgramPrefix)pe;
            if( pf.getChildAt(1) instanceof MethodBodyStatement )
                pe = pf.getChildAt(1);
            else 
                pe = pf.getChildAt(0);
        }

        
        assert( pe instanceof MethodBodyStatement );
        
        //return termFactory.createQuanUpdateTerm
        //    ( boundVars, guards, locs, values, term.sub(1))
        
        System.out.println(pe.toString());
        
        return term.sub(1);
    }
}
