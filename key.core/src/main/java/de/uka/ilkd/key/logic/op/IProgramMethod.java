/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

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

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

public interface IProgramMethod
        extends IObserverFunction, SourceElement, ProgramElement, MemberDeclaration {

    MethodDeclaration getMethodDeclaration();

    /**
     * returns the KeYJavaType of the <tt>i</tt>-th parameter declaration. This method does not care
     * about the invoker as argSort does.
     *
     * @param i the int specifying the parameter position
     * @return the KeYJavaType of the <tt>i</tt>-th parameter
     */
    KeYJavaType getParameterType(int i);

    StatementBlock getBody();

    /**
     * Test whether the declaration is a constructor.
     */
    boolean isConstructor();

    /**
     * Test whether the declaration is model.
     */
    boolean isModel();

    boolean isVoid();

    /**
     * @return the return type
     */
    KeYJavaType getReturnType();

    ProgramElementName getProgramElementName();

    String getUniqueName();

    String getFullName();

    String getName();

    boolean isAbstract();

    boolean isImplicit();

    boolean isNative();

    boolean isFinal();

    boolean isSynchronized();

    Throws getThrown();

    ParameterDeclaration getParameterDeclarationAt(int index);

    /**
     * Returns the variablespecification of the i-th parameterdeclaration
     */
    VariableSpecification getVariableSpecification(int index);

    int getParameterDeclarationCount();

    ImmutableArray<ParameterDeclaration> getParameters();

    // Methods from OberverFunction, TODO Create interface for ObersverFunction
    ImmutableArray<KeYJavaType> getParamTypes();

    /**
     * @return The list of {@link LocationVariable}s passed as parameters to this
     *         {@link IProgramMethod}.
     */
    ImmutableList<LocationVariable> collectParameters();
}
