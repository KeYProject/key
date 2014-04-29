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

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 * A &93;bigint literal
 * @author bruns
 *
 */
public final class BigintLiteral extends Literal {

    /**
     *      Textual representation of the value.
     */
    private String value;

    public BigintLiteral() {
        this(0);
    }

    public BigintLiteral(int value) {
        this(""+value);
    }

    public BigintLiteral(String value) {
        assert value != null : "cannot create literal with null value";
        this.value=value.intern();
    }
    
    public BigintLiteral(BigInteger value){
        this(value.toString());
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     *     May contain: Comments
     */
    public BigintLiteral(ExtList children) {
        super(children);
        this.value= ""+0;
    }
    
    /**
	 * Constructor for Recoder2KeY transformation.
	 * 
	 * @param children
	 *            the children of this AST element as KeY classes, may contain:
	 *            Comments
	 * @param value
	 *            the value of the literal
	 */
	public BigintLiteral(ExtList children, String value) {
		super(children);
    	this.value = value.intern();
    }

    /**
     *      Get value.
     *      @return the string.
     */
    public String getValue() {
        return value;
    }


    /** tests if equals
     */
    @Override
    public boolean equalsModRenaming
	( SourceElement o, NameAbstractionTable nat) {
	if (!(o instanceof BigintLiteral)) {
	    return false;
	}
	return ((BigintLiteral)o).getValue().equals(getValue()); 
    }
    
    @Override
    public boolean equals(Object o){
    	if (o instanceof BigintLiteral)
    	    return value.equals(((BigintLiteral)o).getValue());
    	else
    	    return false;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        assert false : "unexpected visitor "+v+" of "+v.getClass();
//        v.performActionOnBigintLiteral(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printBigintLiteral(this);
    }


    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
    }

}