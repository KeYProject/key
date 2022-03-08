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

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;

import javax.annotation.Nullable;
import java.util.List;


public class EmptySetLiteral extends Literal {
    public static final EmptySetLiteral LOCSET = new EmptySetLiteral(null, null);

    public EmptySetLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments) {
        super(pi, comments);
    }

    @Override
    public boolean equalsModRenaming(SourceElement o,
                                     NameAbstractionTable nat) {
        return o == this;
    }


    public void visit(Visitor v) {
        v.performActionOnEmptySetLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEmptySetLiteral(this);
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
