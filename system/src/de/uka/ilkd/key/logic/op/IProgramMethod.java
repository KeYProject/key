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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.Throws;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.logic.ProgramElementName;

public interface IProgramMethod extends IObserverFunction, SourceElement, ProgramElement, MemberDeclaration {

   public abstract MethodDeclaration getMethodDeclaration();

   /**     
    * returns the KeYJavaType of the <tt>i</tt>-th paramter declaration. This method 
    * does not care about the invoker as argSort does.      
    * @param i the int specifying the parameter position
    * @return the KeYJavaType of the <tt>i</tt>-th parameter
    */
   public abstract KeYJavaType getParameterType(int i);

   public abstract StatementBlock getBody();

   /**
    * Test whether the declaration is a constructor.
    */
   public abstract boolean isConstructor();

   /**
    * Test whether the declaration is model.
    */
   public abstract boolean isModel();

   public abstract boolean isVoid();

   /**
    * @return the return type
    */
   public abstract KeYJavaType getReturnType();

   public abstract ProgramElementName getProgramElementName();

   public abstract String getFullName();

   public abstract String getName();

   public abstract boolean isAbstract();

   public abstract boolean isImplicit();

   public abstract boolean isNative();

   public abstract boolean isFinal();

   public abstract boolean isSynchronized();

   public abstract Throws getThrown();

   public abstract ParameterDeclaration getParameterDeclarationAt(int index);

   /** 
    * Returns the variablespecification of the i-th parameterdeclaration 
    */
   public abstract VariableSpecification getVariableSpecification(int index);

   public abstract int getParameterDeclarationCount();

   public abstract ImmutableArray<ParameterDeclaration> getParameters();

   // Methods from OberverFunction, TODO Create interface for ObersverFunction
   public ImmutableArray<KeYJavaType> getParamTypes();
}