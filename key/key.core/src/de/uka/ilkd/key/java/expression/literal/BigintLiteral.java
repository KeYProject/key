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

import java.math.BigInteger;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * A <code>&#92;bigint</code> literal
 * @author bruns
 *
 */
public final class BigintLiteral extends AbstractIntegerLiteral {

    /**
     * Textual representation of the value as a decimal number.
     */
    private final String valueStr;

    /**
     * The actual value of the literal.
     */
    private final BigInteger value;

    /**
     * Creates a new BigintLiteral representing the given int value.
     * @param value the value of the literal
     */
    public BigintLiteral(int value) {
        this.value = BigInteger.valueOf(value);
        valueStr = this.value.toString().intern();
    }

    /**
     * Creates a new BigintLiteral from the given String. The input may be any String containing a
     * decimal literal. In addition, a preceding '-' sign is allowed.
     *
     * @param valStr the String that contains the literal
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *          literal
     */
    public BigintLiteral(String valStr) {
        super(false);
        assert valStr != null : "cannot create literal with null value";
        value = new BigInteger(valStr);
        this.valueStr = value.toString().intern();
    }

    /**
     * Creates a new BigintLiteral representing the given value.
     *
     * @param value the value of the literal
     */
    public BigintLiteral(BigInteger value) {
        super(false);
        assert value != null : "cannot create literal with null value";
        this.value = value;
        this.valueStr = value.toString().intern();
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */
    public BigintLiteral(ExtList children) {
        super(children, false);
        value = BigInteger.ZERO;
        valueStr = "0".intern();
    }

    /**
     * Constructor for Recoder2KeY transformation.
     *
     * @param children the children of this AST element as KeY classes, may contain: Comments
     * @param valStr the value of the literal
     *
     */
    public BigintLiteral(ExtList children, String valStr) {
        super(children, false);
        value = new BigInteger(valStr);
        this.valueStr = value.toString().intern();
    }

//    @Override
//    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
//        if (!(o instanceof BigintLiteral)) {
//            return false;
//        }
//        return ((BigintLiteral)o).getValueString().equals(getValueString());
//    }

    // TODO:
//    @Override
//    public boolean equals(Object o) {
//        if (o instanceof BigintLiteral) {
//            return valueStr.equals(((BigintLiteral)o).getValueString());
//        } else {
//            return false;
//        }
//    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnBigintLiteral(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printBigintLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
    }

    @Override
    public BigInteger getValue() {
        return value;
    }

    @Override
    public String getValueString() {
        return valueStr;
    }
}
