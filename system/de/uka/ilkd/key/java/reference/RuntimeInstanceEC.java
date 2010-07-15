// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                          Universitaet Koblenz-Landau, Germany
//                          Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

public class RuntimeInstanceEC extends JavaNonTerminalProgramElement 
      {

     private final ReferencePrefix runtimeInstance;

     public RuntimeInstanceEC(ReferencePrefix expression) {
	 assert expression != null;
 	runtimeInstance=expression;
     }

     public RuntimeInstanceEC(ExtList children) {
	 runtimeInstance=(ReferencePrefix)children.get(ReferencePrefix.class);
     }
     
     public ReferencePrefix getReferencePrefix() {
	 return runtimeInstance;
     }

     public void visit(Visitor v) {
 	v.performActionOnRuntimeInstanceEC(this);
     }

     public int getChildCount() {
 	return (runtimeInstance!=null) ? 1 : 0;
     }

     public ProgramElement getChildAt(int index) {
 	if (index==0) return runtimeInstance;
 	return null;
     }
     
     public String toString() {
	 return "[[this=" + runtimeInstance + "]]";
     }

 }
