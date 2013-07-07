// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext.expression.literal;

import java.math.BigDecimal;

import de.uka.ilkd.key.java.recoderext.KeYRecoderExtension;
import de.uka.ilkd.key.util.ExtList;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Literal for JML \real type;
 * @author bruns
 *
 */
public final class RealLiteral extends Literal implements KeYRecoderExtension {

    private static final long serialVersionUID = 7138964492857394183L;
    private String value;

    public RealLiteral (int value){
        this(""+value+".0");
    }

    public RealLiteral(String value){
        this.value = value.intern();
    }

    public RealLiteral(BigDecimal value){
        this(value.toString());
    }

    public RealLiteral(){
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

    public String getValue(){
        return value;
    }

    public String toString(){
        return value;
    }

    public boolean equals(Object o){
        if (o instanceof RealLiteral)
            return value.equals(((RealLiteral)o).getValue());
        else
            return false;
    }

    @Override
    public int hashCode() {
        int hash = -1;
        try {
            hash = (int) Double.parseDouble(value);
        } finally {
            System.err.println("Strange value for BigIntLiteral: " + this);
        }
        return hash;
    }


}