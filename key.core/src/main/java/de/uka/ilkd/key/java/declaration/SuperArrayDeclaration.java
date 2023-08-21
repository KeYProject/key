/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * At the moment the mere purpose of this Class is to provide an encapsulation for the length
 * attribute.
 */
public class SuperArrayDeclaration extends TypeDeclaration {

    private FieldDeclaration length = null;

    private SuperArrayDeclaration(ProgramElementName name, FieldDeclaration length) {
        super(new Modifier[0], name, name, new MemberDeclaration[] { length }, false, false);
        this.length = length;
    }

    public SuperArrayDeclaration(FieldDeclaration length) {
        this(new ProgramElementName("SuperArray"), length);
    }

    public int getChildCount() {
        return 0;
    }

    public boolean isInterface() {
        return false;
    }

    public FieldDeclaration length() {
        return length;
    }

    /**
     * returns the local declared supertypes
     */
    public ImmutableList<KeYJavaType> getSupertypes() {
        return ImmutableSLList.nil();
    }


    public ProgramElement getChildAt(int i) {
        return null;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnSuperArrayDeclaration(this);
    }

}
