// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.ProgramElement;

/**
 * Transforms a method call into an update. Used for strictly pure methods.
 * 
 * @see de.uka.ilkd.key.logic.sort.ProgramSVSort#PUREMETHODBODY
 * @author jseidel
 *
 */

public class MethodCallToUpdate extends AbstractMetaOperator {
    
    /* here we are */
    public MethodCallToUpdate() {
        super(new Name("#methodCallToUpdate"), 2);
    }
    
    /* does all the work */
    public Term calculate( Term term, SVInstantiations svInst, Services services ) {
        
        Debug.out("MethodCallToUpdate.calculate() called.");
        Debug.out("term.sub(0) is of type " + term.sub(0).getClass().getName() + " " +
              "and contains " + term.sub(0).toString() );
        Debug.out("term.sub(1) is of type " + term.sub(1).getClass().getName() + " " +
              "and contains " + term.sub(1).toString() );

        // find SchemaVariable containing our strictly pure method body statement
        IteratorOfEntryOfSchemaVariableAndInstantiationEntry it
            = svInst.pairIterator();
        MethodBodyStatement spmbs = null;
        while( it.hasNext() ) {
            EntryOfSchemaVariableAndInstantiationEntry entry = it.next();
            if( entry.value() instanceof ProgramInstantiation ) {
                ProgramInstantiation pi = (ProgramInstantiation) entry.value();
                ProgramElement pe = pi.getProgramElement();
                
                if( pe instanceof MethodBodyStatement ) {
                    assert( spmbs == null ); // there shouldn't be more than one instantiated method body statement
                    spmbs = (MethodBodyStatement)pe;
                }
            }
        }
        assert( spmbs != null ); // .. and at least one

        // generate term for method's return value
        IProgramVariable method_result = spmbs.getResultVariable();
        Debug.out("Using MethodBodyStatement '" + spmbs.toString() + 
              "' with ResultVariable '"+method_result+"'" +
              " - its designated Context is of Class '" + spmbs.getDesignatedContext().getClass().toString() +
              "'"
              );
  
        Term location = services.getTypeConverter()
         .convertToLogicElement( spmbs.getResultVariable() );
            
        // generate parameter terms for function
        int offset = 0;
        if(!spmbs.isStatic(services)) offset = 1;
        Term[] param = new Term[spmbs.getArguments().size() + offset];
        if(!spmbs.isStatic(services)) {
            param[0] = services.getTypeConverter()
             .convertToLogicElement(spmbs.getDesignatedContext());
        }
        for( int i = 0; i < spmbs.getArguments().size(); i++ ) {
            // arguments should all be simple variables by now... (?)
            param[i+offset] = services.getTypeConverter()
             .convertToLogicElement(spmbs.getArguments().getExpression(i));
        }
        
        // generate a new function
        Term location_value = TermFactory.DEFAULT.createFunctionTerm(
                spmbs.getProgramMethod(services), param );
        
        return TermFactory.DEFAULT.createUpdateTerm(location, location_value, term.sub(1));
        
        //return term.sub(1);
    }
}
