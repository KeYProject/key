// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public abstract class ExpressionOperator extends NonRigidFunction {

    private final Expression expression;

    public ExpressionOperator(Name name, Sort sort, Expression expr) {
	super(name, sort, new PrimitiveSort[0]);
	this.expression=expr;
    }

    public Expression expression() {
	return expression;
    }

    public abstract Term resolveExpression
	(SVInstantiations svInst, Services services);
    

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	// perhaps to pessimistic
	return false;
    }    
}
