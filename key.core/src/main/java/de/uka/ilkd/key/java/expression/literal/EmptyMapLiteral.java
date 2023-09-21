/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.MapLDT;
import de.uka.ilkd.key.logic.Name;

public class EmptyMapLiteral extends Literal {

    public static final EmptyMapLiteral INSTANCE = new EmptyMapLiteral();

    private EmptyMapLiteral() {
    }

    @Override
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        return o == this;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnEmptyMapLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_MAP);
    }

    @Override
    public Name getLDTName() {
        return MapLDT.NAME;
    }

}
