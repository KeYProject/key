/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.expression.literal;

import java.math.BigDecimal;

import de.uka.ilkd.key.java.recoderext.KeYRecoderExtension;

import org.key_project.util.ExtList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Literal for JML \real type;
 *
 * @author bruns
 *
 */
public final class RealLiteral extends Literal implements KeYRecoderExtension {

    private static final long serialVersionUID = 7138964492857394183L;
    private static final Logger LOGGER = LoggerFactory.getLogger(RealLiteral.class);
    private final String value;

    public RealLiteral(int value) {
        this(value + ".0");
    }

    public RealLiteral(String value) {
        this.value = value.intern();
    }

    public RealLiteral(BigDecimal value) {
        this(value.toString());
    }

    public RealLiteral() {
        this("0.0");
    }

    public RealLiteral(ExtList el) {
        this();
    }

    @Override
    public Object getEquivalentJavaType() {
        return null;
    }

    @Override
    public Expression deepClone() {
        return this;
    }

    @Override
    public void accept(SourceVisitor arg0) {
        // TODO Auto-generated method stub

    }

    public String getValue() {
        return value;
    }

    public String toString() {
        return value;
    }

    public boolean equals(Object o) {
        if (o instanceof RealLiteral) {
            return value.equals(((RealLiteral) o).getValue());
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        int hash = -1;
        try {
            hash = (int) Double.parseDouble(value);
        } finally {
            LOGGER.warn("Strange value for BigIntLiteral: " + this);
        }
        return hash;
    }


}
