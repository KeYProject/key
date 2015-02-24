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

package de.uka.ilkd.key.java.recoderext.expression.literal;

import java.math.BigInteger;

import de.uka.ilkd.key.java.recoderext.KeYRecoderExtension;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public final class BigintLiteral extends Literal implements KeYRecoderExtension {
    
    private static final long serialVersionUID = 4746776922960563934L;
    private String value;
    
    public BigintLiteral (int value){
        this(""+value);
    }
    
    public BigintLiteral( String value){
        this.value = value.intern();
    }
    
    public BigintLiteral(BigInteger value){
        this(value.toString());
    }
    
    public BigintLiteral(){
        this(0);
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
        if (o instanceof BigintLiteral)
            return value.equals(((BigintLiteral)o).getValue());
        else
            return false;
    }

    @Override
    public int hashCode() {
        int hash = -1;
        try { 
            hash = (int) Long.parseLong(value);
        } finally {
            System.err.println("Strange value for BigIntLiteral: " + this);
        }
        return hash;
    }
  

}