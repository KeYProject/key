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

package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.TerminalProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Modifier.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public abstract class Modifier extends JavaProgramElement implements TerminalProgramElement {

    /**
     *      Modifier.
     */

    public Modifier() {}

    /**
     *      Modifier. 
     * @param children May contain: some Comments
     */
    public Modifier(ExtList children) {
	super(children);
    }

    /**
     *      Get symbol.
     *      @return the string.
     */

    protected abstract String getSymbol();

    /**
 *        Get symbol text.
 *        @return the symbol text.
     */
    public String getText() {
	return getSymbol();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnModifier(this);
    }
    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printModifier(this);
    }
}