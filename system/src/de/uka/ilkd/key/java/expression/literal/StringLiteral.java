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

package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;


public class StringLiteral extends Literal implements ReferencePrefix {

    protected final String value;


    /**
     * String literal.
     * @param value a string.
     */
    public StringLiteral(String value) {
        this.value=value;
    }

    /**
     * String literal.
     * @param children an ExtList with children(here:comments)
     * @param value a string.
     */
    public StringLiteral(ExtList children, String value) {
	super(children);
        this.value=value;
    }


    public boolean equalsModRenaming(SourceElement o, 
	    			     NameAbstractionTable nat) {
	if (!(o instanceof StringLiteral)) {
	    return false;
	}
	return ((StringLiteral)o).getValue().equals(getValue()); 
    }
    
    public int hashCode() {
    	int result = 17;
    	result = 37 * result + getValue().hashCode();
    	return result;
    }
    
    public boolean equals(Object o) {
    	return super.equals(o);
    }


    public String getValue() {
        return value;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnStringLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printStringLiteral(this);
    }


    /**
     * We do not have a prefix, so fake it!
     * This way we implement ReferencePrefix
     * @author VK
     */
    public ReferencePrefix getReferencePrefix() {
	return null;
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
	return this;
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
	return javaServ.getJavaInfo().getKeYJavaType("java.lang.String");
    }
}