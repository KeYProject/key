// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.visitor;

import java.io.StringWriter;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.CompilableJavaCardPP;
import de.uka.ilkd.key.util.ExtList;

/**
 * Replaces array references a[expr] by a[dat] where dat is the concrete value
 * for expr. This is needed for unit test generation.
 */
public class IndexReplaceVisitor extends CreatingASTVisitor {

    private ProgramElement result = null;
    // private KeYJavaType containingKJT=null
    private final Expression[][] testLocation;
    private final boolean singleTuple;
    private final ProgramVariable partCounter;
    // private ProgramVariable[] lCounter;
    private final ProgramVariable[] testArray;

    public IndexReplaceVisitor(final ProgramElement pe,
	    final Expression[][] testLocation, final boolean singleTuple,
	    final ProgramVariable partCounter,
	    // ProgramVariable[] lCounter,
	    final ProgramVariable[] testArray, final Services services) {
	super(pe, true, services);
	this.testLocation = testLocation;
	this.singleTuple = singleTuple;
	this.partCounter = partCounter;
	// this.lCounter = lCounter;
	this.testArray = testArray;
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

    private Expression tryToReplaceByTestDatum(final Expression e) {
	final int i = findLocIndex(e);
	if (i != -1) {
	    final Expression testDat = singleTuple ? testArray[i]
		    : new ArrayReference(testArray[i],
		            new Expression[] { partCounter });
	    return testDat;
	}
	return e;
    }

    private int findLocIndex(final Expression e) {
	final StringWriter sw = new StringWriter();
	final CompilableJavaCardPP cjpp = new CompilableJavaCardPP(sw, true);
	for (int i = 0; i < testLocation.length; i++) {
	    for (int j = 0; j < testLocation[i].length; j++) {
		final Expression testLoc = testLocation[i][j];
		String testLocStr, eStr;
		if (testLoc instanceof JavaSourceElement) {
		    testLocStr = ((JavaSourceElement) testLoc).toString(cjpp,
			    sw);
		} else {
		    testLocStr = testLoc.toString();
		}

		if (e instanceof JavaSourceElement) {
		    eStr = ((JavaSourceElement) e).toString(cjpp, sw);
		} else {
		    eStr = e.toString();
		}

		if (testLocStr.equals(eStr)) {
		    return i;
		}
	    }
	}
	return -1;
    }

    @Override
    public void performActionOnArrayReference(final ArrayReference x) {
	final ExtList changeList = stack.peek();
	if (changeList.getFirst() == CHANGED) {
	    changeList.removeFirst();
	}
	changeList.removeFirstOccurrence(PositionInfo.class);
	final ReferencePrefix rp = (ReferencePrefix) changeList.get(0);
	final ImmutableArray<Expression> aoe = x.getDimensionExpressions();
	final Expression[] indices = new Expression[aoe.size()];
	for (int i = 0; i < aoe.size(); i++) {
	    indices[i] = tryToReplaceByTestDatum(aoe.get(i));
	}
	final ArrayReference ar = new ArrayReference(rp, indices);
	addChild(ar);
	changed();
    }

}
