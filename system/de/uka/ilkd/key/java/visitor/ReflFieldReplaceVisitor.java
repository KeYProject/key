// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.ArrayLengthReference;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.unittest.AccessMethodsManager;
import de.uka.ilkd.key.util.ExtList;

/**
 * @author mbender
 * 
 */
public class ReflFieldReplaceVisitor extends FieldReplaceVisitor {

    AccessMethodsManager amm;

    public ReflFieldReplaceVisitor(final ProgramElement pe,
	    final Services services) {
	super(pe, services);
	amm = AccessMethodsManager.getInstance();
    }

    @Override
    @SuppressWarnings("unchecked")
    public void performActionOnFieldReference(final FieldReference x) {
	final ExtList changeList = stack.peek();
	if (changeList.getFirst() == CHANGED) {
	    changeList.removeFirst();
	}
	changeList.removeFirstOccurrence(PositionInfo.class);
	if (x.getReferencePrefix() != null) {
	    final Expression field = (Expression) changeList.get(1);
	    if (field instanceof ProgramVariable) {
		final String shortName = ((ProgramVariable) field)
		        .getProgramElementName().getProgramName();
		if ("length".equals(shortName)) {
		    final ExtList l = new ExtList();
		    l.add(changeList.get(0));
		    addChild(new ArrayLengthReference(l));
		} else {
		    assert x instanceof FieldReference;
		    addChild(amm.callGetter(x));
		}
	    }
	} else {
	    String typeName = ((ProgramVariable) x.getChildAt(0))
		    .getKeYJavaType().getName();
	    typeName = PrettyPrinter.getTypeNameForAccessMethods(typeName);
	    addChild(new MethodReference(new ExtList(), new ProgramElementName(
		    "_"
		            + ((ProgramVariable) changeList.get(0))
		                    .getProgramElementName().getProgramName()
		            + typeName), null));
	}
	changed();
    }

}
