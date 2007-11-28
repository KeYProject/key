// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser.jml;

import de.uka.ilkd.key.jml.WrongIntSemanticsException;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;

public class DefaultArithOpProvider implements ArithOpProvider{

    protected Namespace functions;
    private boolean javaSemantics;

    public DefaultArithOpProvider(Namespace functions, boolean javaSemantics){
	this.functions = functions;
        this.javaSemantics = javaSemantics;
    }

    public Namespace getFunctions(){
	return functions;
    }

    public boolean javaSemantics(){
	return javaSemantics;
    }
    
    public void setFunctions(Namespace functions){
	this.functions = functions;
    }

    public Function getMin(boolean l){
	return getFunction(l, "long_MIN", "int_MIN", null, "minimum");
    }

    public Function getMax(boolean l){
	return getFunction(l, "long_MAX", "int_MAX", null, "maximum");
    }
    
    public Function getAdd(boolean l){
	return getFunction(l, "addJlong", "addJint", "add", "addition");
    }

    public Function getSub(boolean l){
	return getFunction(l, "subJlong", "subJint", "sub", "subtraction");
    }

    public Function getMinus(boolean l){
	return getFunction(l, "unaryMinusJlong", "unaryMinusJint", "neg", 
			   "negation");
    }

    public Function getMul(boolean l){
	return getFunction(l, "mulJlong", "mulJint", "mul", "multiplication");
    }

    public Function getDiv(boolean l){
	return getFunction(l, "divJlong", "divJint", "jdiv", "division");
    }

    public Function getMod(boolean l){
	return getFunction(l, "modJlong", "modJint", "jmod", "modulo");
    }

    public Function getOr(boolean l){
	return getFunction(l, "orJlong", "orJint", "binaryOr", "bitwise or");
    }

    public Function getAnd(boolean l){
	return getFunction(l, "andJlong", "andJint", "binaryAnd", "bitwise and");
    }

    public Function getXor(boolean l){
	return getFunction(l, "xorJlong", "xorJint", "binaryXor", "bitwise xor");
    }

    public Function getNeg(boolean l){
	return getFunction(l, "negJlong", "negJint", "invertBits", 
			   "bitwise negation");
    }

    public Function getShiftRight(boolean l){
	return getFunction(l, "shiftrightJlong", "shiftrightJint", 
			   "binaryShiftRight", "shift right");
    }

    public Function getShiftLeft(boolean l){
	return getFunction(l, "shiftleftJlong", "shiftleftJint", 
			   "binaryShiftLeft", "shift left");
    }

    public Function getUnsignedShiftRight(boolean l){
	return getFunction(l, "unsignedshiftrightJlong", 
			   "unsignedshiftrightJint", "binaryUnsignedShiftRight",
			   "unsigned shift right");
    }

    public Function getCastToByte(){
	return (Function) functions.lookup(new Name("moduloByte"));
    }

    public Function getCastToShort(){
	return (Function) functions.lookup(new Name("moduloShort"));
    }


    public Function getCastToInt(){
	return (Function) functions.lookup(new Name("moduloInt"));
    }

    public Function getCastToLong(){
	return (Function) functions.lookup(new Name("moduloLong"));
    }

    protected Function getFunction(boolean l, String sLong, String sInt, 
				 String sDefault, String description){
	Function f = null;
	if (javaSemantics) {
            if (l){
                f = (Function) functions.lookup(new Name(sLong));
            }else{
                f = (Function) functions.lookup(new Name(sInt));	    
            }
        } else {
	   f = (Function) functions.lookup(new Name(sDefault));
        }
        
	if(f == null){
	    throw new WrongIntSemanticsException(description);
	}
	return f;
    }


}
