// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;
import recoder.java.expression.operator.CopyAssignment;



public class SetAssignment extends Assignment {
    
    public SetAssignment() {
        // nothing to do
    }
            
     public SetAssignment(Expression lhs, Expression rhs) {
         super(lhs, rhs);
         makeParentRoleValid();
     }
     

     protected SetAssignment(SetAssignment proto) {
         super(proto);
         makeParentRoleValid();
     }
     
     
     public SetAssignment(CopyAssignment proto) {
         super(proto);
         makeParentRoleValid();
     }


     public SetAssignment deepClone() {
         return new SetAssignment(this);
     }
     

     public int getArity() {
         return 2;
     }

     
     public int getPrecedence() {
         return 13;
     }

     
     public int getNotation() {
         return INFIX;
     }


     public void accept(SourceVisitor v) {
     }
 }
