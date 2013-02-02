// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;

public class Comment extends JavaSourceElement {

    private final String text;

    public Comment() {
	this.text = null;
    }

    public Comment(String text) {
	this.text = text;
    }

    public Comment(String text, PositionInfo pInfo) {
        super(pInfo);
        this.text = text;
    }

    public boolean isPrefixed () {
	return false;
    }

    public void prettyPrint(PrettyPrinter w) {
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
    }

    public String getText(){
	return text;
    }
    
    
    public String toString() {
        return getText();
    }


    /** comments can be ignored
     */
     public boolean equalsModRenaming(SourceElement se, 
				      NameAbstractionTable nat) {
     	return true;
     }
     
     public int hashCode(){
     	int result = 17;
     	result = 37 * result + getText().hashCode();
     	return result;
     }
     
     public boolean equals(Object o){
     	if (o == this)
     		return true;
     	if(!(o instanceof Comment))
     		return false;
     	Comment cmp = (Comment)o;
     	return (getText().equals(cmp.getText()));
     }
}
