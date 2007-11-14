package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.EntryOfSchemaVariableAndInstantiationEntry;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.IteratorOfEntryOfSchemaVariableAndInstantiationEntry;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.ProgramInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.rule.inst.ProgramInstantiation;

/**
 * Transforms a method call into an update. Used for strictly pure methods.
 * 
 * @author jseidel
 *
 */

public class MethodCallToUpdate extends AbstractMetaOperator {
    
    /* printf-style "debugging"... */
    static void debug( String s ) {
        System.out.println(s);          
    }
    
    public MethodCallToUpdate() {
        super(new Name("#methodCallToUpdate"), 2);
    }
    
    public Term calculate( Term term, SVInstantiations svInst, Services services ) {
        
        debug("MethodCallToUpdate.calculate() called.");
        debug("term.sub(0) is of type " + term.sub(0).getClass().getName() + " " +
              "and contains " + term.sub(0).toString() );
        debug("term.sub(1) is of type " + term.sub(1).getClass().getName() + " " +
              "and contains " + term.sub(1).toString() );
        //System.out.println("term.sub(2) is of type " + term.sub(2).getClass().getName() );

        IteratorOfEntryOfSchemaVariableAndInstantiationEntry it
            = svInst.pairIterator();
        MethodBodyStatement spmbs = null;
        while( it.hasNext() ) {
            EntryOfSchemaVariableAndInstantiationEntry entry = it.next();
            if( entry.value() instanceof ProgramInstantiation ) {
                ProgramInstantiation pi = (ProgramInstantiation) entry.value();
                ProgramElement pe = pi.getProgramElement();
                
                if( pe instanceof MethodBodyStatement ) {
                    assert( spmbs == null ); // there shouldn't be more than one instanciated method body statement
                    spmbs = (MethodBodyStatement)pe;
                }
            }
        }
        
        assert( spmbs != null ); // .. and at least one
        
        debug(spmbs.toString());
        
        IProgramVariable method_result = spmbs.getResultVariable();
        
        
        //Term location = TermFactory.DEFAULT.createVariableTerm( spmbs.getResultVariable(). );
        //Term location_value;
        
        //return TermFactory.DEFAULT.createUpdateTerm(location, location_value, term.sub(1));
        
        return term.sub(1);
    }
}
