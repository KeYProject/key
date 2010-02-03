// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ListOfSchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class WhileInvRuleWrapper extends While implements MetaConstructWithSV {

    private Term wrappedElement;


    public WhileInvRuleWrapper(Term t) {
	wrappedElement = t;
    }


    public Term unwrap() {
	return wrappedElement;
    }


    public ListOfSchemaVariable neededInstantiations(SVInstantiations svInst) {
        Term t = unwrap();
        JavaProgramElement jpe = t.sub(0).javaBlock().program();
        WhileInvRule wir = (WhileInvRule) t.op();
        return wir.neededInstantiations(jpe, svInst);
    }

}
