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
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.logic.Name;
import org.key_project.util.ExtList;

import javax.annotation.Nullable;
import java.util.List;


public final class StringLiteral extends Literal implements ReferencePrefix {
    private final String value;

    public StringLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments, String value) {
        super(pi, comments);
        this.value = value;
    }

    /**
     * String literal.
     *
     * @param value a string.
     */
    public StringLiteral(String value) {
        this(null, null, value);
    }

    /**
     * String literal.
     *
     * @param children an ExtList with children(here:comments)
     * @param value    a string.
     */
    public StringLiteral(ExtList children, String value) {
        super(children);
        this.value = value;
    }


    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        if (!(o instanceof StringLiteral)) {
            return false;
        }
        return ((StringLiteral) o).getValue().equals(getValue());
    }

    @Override
    public int computeHashCode() {
        return 17 * super.computeHashCode() + getValue().hashCode();
    }

    public String getValue() {
        return value;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnStringLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printStringLiteral(this);
    }


    /**
     * We do not have a prefix, so fake it!
     * This way we implement ReferencePrefix
     *
     * @author VK
     */
    public ReferencePrefix getReferencePrefix() {
        return null;
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
        return this;
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType("java.lang.String");
    }

    @Override
    public Name getLDTName() {
        return CharListLDT.NAME;
    }
}
