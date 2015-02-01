// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.*;

/**
 * Variable condition that enforces a given generic sort to be instantiated with
 * the type of a field constant.
 * 
 * The condition can only be fulfilled if the given field term is constant of
 * which the referred type is known.
 */
public final class FieldTypeToSortCondition implements VariableCondition {

    private final SchemaVariable exprOrTypeSV;
    private final GenericSort sort;

    public FieldTypeToSortCondition(final SchemaVariable exprOrTypeSV,
                                   final GenericSort sort) {
        this.exprOrTypeSV = exprOrTypeSV;
        this.sort = sort;
        assert checkSortedSV(exprOrTypeSV);
    }

    public static boolean checkSortedSV(final SchemaVariable exprOrTypeSV) {
        final Sort svSort = exprOrTypeSV.sort();
        if (svSort == ProgramSVSort.EXPRESSION
                || svSort == ProgramSVSort.SIMPLEEXPRESSION
                || svSort == ProgramSVSort.NONSIMPLEEXPRESSION
                || svSort == ProgramSVSort.TYPE
                || exprOrTypeSV.arity() == 0) {
            return true;
        }
        return false;
    }

    @Override
    public MatchConditions check(SchemaVariable var,
                                 SVSubstitute svSubst,
                                 MatchConditions matchCond,
                                 Services services) {
            
        if (var != exprOrTypeSV) {
            return matchCond;
        }

        final SVInstantiations inst = matchCond.getInstantiations();

        if (svSubst instanceof Term) {
            Operator op = ((Term) svSubst).op();
            if (op instanceof Function) {
                String name = op.name().toString();
                
                String className;
                String attributeName;
                
                // check for normal attribute
                int endOfClassName = name.indexOf("::$");                
                
                int startAttributeName = endOfClassName + 3;                
                
                     
                if ( endOfClassName < 0) {
                        // not a normal attribute, maybe an implicit attribute like <created>?
                        endOfClassName = name.indexOf("::<");
                        startAttributeName = endOfClassName + 2;
                }

                if ( endOfClassName < 0 ) {
                        return null;
                }
    

                className     = name.substring(0, endOfClassName);
                attributeName = name.substring(startAttributeName);

                ProgramVariable attribute = services.getJavaInfo()
                        .getAttribute(attributeName, className);
                
                if (attribute == null) {
                    return null;
                }

                Sort targetSort = attribute.getKeYJavaType().getSort();
                
                return matchCond.setInstantiations(inst.add(
                        GenericSortCondition.createIdentityCondition(sort,
                                targetSort),
                        services));
            }
        }

        return null;
    }

    @Override
    public String toString() {
        return "\\fieldType(" + exprOrTypeSV + ", " + sort + ")";
    }
}