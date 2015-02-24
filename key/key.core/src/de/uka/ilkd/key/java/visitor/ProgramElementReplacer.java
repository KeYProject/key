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

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.ExtList;

public class ProgramElementReplacer extends CreatingASTVisitor {

    private ProgramElement oldElement;
    private ProgramElement newElement;
    private boolean done;

    public ProgramElementReplacer(JavaProgramElement program, Services services)
    {
        super(program, false, services);
    }

    public ProgramElement replace(ProgramElement oldElement, ProgramElement newElement)
    {
        this.oldElement = oldElement;
        this.newElement = newElement;
        done = false;
        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        return el.get(ProgramElement.class);
    }

    protected void doAction(ProgramElement element)
    {
        if (!done && element == oldElement) {
            done = true;
            addChild(newElement);
            changed();
        }
        else {
            super.doAction(element);
        }
    }

}