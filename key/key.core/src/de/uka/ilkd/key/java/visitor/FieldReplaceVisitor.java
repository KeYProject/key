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

package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.ArrayLengthReference;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.ExtList;

/**
 * Replaces field references o.a by methodcalls o._a(). This is needed for unit
 * test generation.
 */
public class FieldReplaceVisitor extends CreatingASTVisitor {

    private ProgramElement result = null;

    // private KeYJavaType containingKJT=null

    public FieldReplaceVisitor(final ProgramElement pe, final Services services) {
	super(pe, true, services);
    }

    /** starts the walker */
    @Override
    public void start() {
	stack.push(new ExtList());
	walk(root());
	final ExtList el = stack.peek();
	int i = 0;
	while (!(el.get(i) instanceof ProgramElement)) {
	    i++;
	}
	result = (ProgramElement) stack.peek().get(i);
    }

    public ProgramElement result() {
	return result;
    }

    @Override
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
		    String typeName = ((ProgramVariable) x.getChildAt(1))
			    .getKeYJavaType().getName();
		    typeName = PrettyPrinter
			    .getTypeNameForAccessMethods(typeName);
		    addChild(new MethodReference(new ExtList(),
			    new ProgramElementName("_" + shortName + typeName),
			    (ReferencePrefix) changeList.get(0)));
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