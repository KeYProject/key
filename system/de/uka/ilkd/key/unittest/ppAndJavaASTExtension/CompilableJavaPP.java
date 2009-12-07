// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.ppAndJavaASTExtension;

import java.io.Writer;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * @author mbender
 * 
 */
public class CompilableJavaPP extends CompilableJavaCardPP {

    /**
     * 
     */
    public CompilableJavaPP(final Writer o, final boolean noLinefeed) {
	super(o, noLinefeed);
    }

    @Override
    public void printFieldDeclaration(final FieldDeclaration x)
	    throws java.io.IOException {
	if (!((ProgramVariable) x.getVariables().last().getProgramVariable())
	        .isImplicit()) {
	    printHeader(x);
	    int m = 0;
	    if (x.getModifiers() != null) {
		ImmutableArray<Modifier> mods = x.getModifiers();
		m = mods.size();
		if (x.isFinal()
		        && (!x.isStatic() || !(x.getVariables().get(0)
		                .getProgramVariable() instanceof ProgramConstant))) {
		    m--;
		    mods = removeFinal(mods);
		}
		writeKeywordList(mods);
	    }
	    writeElement((m > 0) ? 1 : 0, x.getTypeReference());
	    final ImmutableArray<? extends VariableSpecification> varSpecs = x
		    .getVariables();
	    assert varSpecs != null : "Strange: a field declaration without a"
		    + " variable specification";
	    writeCommaList(0, 0, 1, varSpecs);
	    write(";");
	    printFooter(x);
	}
    }

}
