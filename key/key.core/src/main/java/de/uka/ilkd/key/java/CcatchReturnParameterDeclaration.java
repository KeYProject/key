// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import java.io.IOException;
import java.util.List;

/**
 * A "\Return" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchReturnParameterDeclaration extends CcatchNonstandardParameterDeclaration {

    public CcatchReturnParameterDeclaration(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
    }

    public CcatchReturnParameterDeclaration(ExtList children) {
        super(null, null);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatchReturnParameterDeclaration(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printCcatchReturnParameterDeclaration(this);
    }

}
