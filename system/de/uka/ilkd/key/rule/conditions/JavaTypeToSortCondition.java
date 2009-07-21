// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.SortException;
import de.uka.ilkd.key.util.Debug;


/**
 * Variable condition that enforces a given generic sort to be instantiated with
 * the sort of a program expression a schema variable is instantiated with
 * (currently only schema variables <code>ProgramSVSort.EXPRESSION</code> are
 * supported)
 */
public class JavaTypeToSortCondition implements VariableCondition {

    private final SchemaVariable exprOrTypeSV;
    private final GenericSort    sort;
    
    public JavaTypeToSortCondition (final SchemaVariable exprOrTypeSV,
                                    final GenericSort sort) {
        this.exprOrTypeSV = exprOrTypeSV;
        this.sort = sort;
        
        if (!checkSortedSV(exprOrTypeSV)) {
            throw new RuntimeException
            ( "Expected a program schemavariable for expressions" );
        }
    }


    public static boolean checkSortedSV(final SchemaVariable exprOrTypeSV) {
        final Sort svSort = exprOrTypeSV.sort ();
        if (svSort == ProgramSVSort.EXPRESSION
             || svSort == ProgramSVSort.SIMPLEEXPRESSION
             || svSort == ProgramSVSort.NONSIMPLEEXPRESSION
             || svSort == ProgramSVSort.TYPE
             || exprOrTypeSV.arity() == 0)  {
            return true;
        }
        return false;
    }
  
    
    /**
     * checks if the condition for a correct instantiation is fulfilled
     * 
     * @param var
     *            the template Variable to be instantiated
     * @param matchCond
     *            the MatchCondition with the current matching state and in
     *            particular the SVInstantiations that are already known to be
     *            needed
     * @param services
     *            the program information object
     * @return modified match results if the condition can be satisfied, or
     *         <code>null</code> otherwise
     */
    public MatchConditions check (SchemaVariable var,
                                  SVSubstitute svSubst,
                                  MatchConditions matchCond,
                                  Services services) {
        if ( var != exprOrTypeSV ) {
            return matchCond;
        }
        
        Debug.assertTrue ( svSubst instanceof Expression || 
                svSubst instanceof TypeReference ||
                svSubst instanceof Term);
        
        final SVInstantiations inst = matchCond.getInstantiations ();
        final Sort type;
        if (svSubst instanceof Term) {
            type = ((Term)svSubst).sort();
        } else if (svSubst instanceof TypeReference) {
            type = ((TypeReference)svSubst).getKeYJavaType().getSort();
        } else {
            final Expression expr = (Expression)svSubst;          
            type = expr.getKeYJavaType ( services, inst.getExecutionContext () ).getSort();
        }
        try {
            return matchCond.setInstantiations ( inst.add
                ( GenericSortCondition.createIdentityCondition
                                                  ( sort, type ) ) );
        } catch ( SortException e ) {
            return null;
        }        
    }

    public String toString () {
        return "\\hasSort(" + exprOrTypeSV + ", " + sort + ")";
    }
}
