/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;



public non-sealed class EmptySetLiteral extends Literal {

    public static final EmptySetLiteral LOCSET = new EmptySetLiteral();


    @Override
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        return o == this;
    }


    public void visit(Visitor v) {
        v.performActionOnEmptySetLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
        PrimitiveType type = PrimitiveType.JAVA_LOCSET;
        return javaServ.getJavaInfo().getKeYJavaType(type);
    }

    @Override
    public Name getLDTName() {
        return LocSetLDT.NAME;
    }
}
