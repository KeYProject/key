/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.FreeLDT;
import de.uka.ilkd.key.logic.Name;

public class FreeLiteral extends Literal {

    public final static FreeLiteral INSTANCE = new FreeLiteral();

    @Override
    public void visit(Visitor v) {
        // TODO Auto-generated method stub

    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_FREE_ADT);
    }

    @Override
    public Name getLDTName() {
        return FreeLDT.NAME;
    }

}
