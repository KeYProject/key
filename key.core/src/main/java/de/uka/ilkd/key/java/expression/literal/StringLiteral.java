/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.logic.Name;

import org.key_project.util.ExtList;


public class StringLiteral extends Literal implements ReferencePrefix {

    protected final String value;


    /**
     * String literal.
     *
     * @param value a string.
     */
    public StringLiteral(String value) {
        this.value = value;
    }

    /**
     * String literal.
     *
     * @param children an ExtList with children(here:comments)
     * @param value a string.
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
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnStringLiteral(this);
    }


    /**
     * We do not have a prefix, so fake it! This way we implement ReferencePrefix
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
