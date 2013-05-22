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


package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.BigintLiteral;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.LongLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;


/** 
 * This class inherits from LDT and implements all method that are
 * necessary to handle integers, shorts and bytes. It caches the symbols 
 * declared in integerHeader.key and offers methods to convert java
 * number types to their logic counterpart.
 */
@SuppressWarnings("unused")
public final class IntegerLDT extends LDT {
    
    public static final Name NAME = new Name("int");    
    
    //public name constants
    public static final String NEGATIVE_LITERAL_STRING = "neglit";
    public static final Name NUMBERS_NAME = new Name("Z");
    public static final Name CHAR_ID_NAME = new Name("C"); 
    
    //the following fields cache the symbols from integerHeader.key. 
    //(explanations see there)
    private final Function sharp;
    private final Function numberSymbol[] = new Function[10];
    private final Function neglit;    
    private final Function numbers;
    private final Function charID;
    private final Function add;
    private final Function neg;
    private final Function sub;
    private final Function mul;
    private final Function div;
    private final Function mod;
    private final Function bsum;
    private final Function bprod;
//    private final Function min; // handled by the \ifEx operator
//    private final Function max;
    private final Function jdiv;
    private final Function jmod;
    private final Function unaryMinusJint;
    private final Function unaryMinusJlong;
    private final Function addJint;
    private final Function addJlong;
    private final Function subJint;
    private final Function subJlong;
    private final Function mulJint;
    private final Function mulJlong;
    private final Function modJint;
    private final Function modJlong;
    private final Function divJint;
    private final Function divJlong;
    private final Function shiftrightJint;
    private final Function shiftrightJlong;
    private final Function shiftleftJint;
    private final Function shiftleftJlong;
    private final Function unsignedshiftrightJint;
    private final Function unsignedshiftrightJlong;
    private final Function orJint;
    private final Function orJlong;
    private final Function andJint;
    private final Function andJlong;
    private final Function xorJint;
    private final Function xorJlong;
    private final Function moduloByte;
    private final Function moduloShort;
    private final Function moduloInt;
    private final Function moduloLong;
    private final Function moduloChar;
    private final Function javaUnaryMinusInt;
    private final Function javaUnaryMinusLong;
    private final Function javaBitwiseNegation;
    private final Function javaAddInt;
    private final Function javaAddLong;
    private final Function javaSubInt;
    private final Function javaSubLong;
    private final Function javaMulInt;    
    private final Function javaMulLong;
    private final Function javaMod;
    private final Function javaDivInt;
    private final Function javaDivLong;
    private final Function javaShiftRightInt;
    private final Function javaShiftRightLong;
    private final Function javaShiftLeftInt;
    private final Function javaShiftLeftLong;
    private final Function javaUnsignedShiftRightInt;
    private final Function javaUnsignedShiftRightLong;
    private final Function javaBitwiseOrInt;
    private final Function javaBitwiseOrLong;
    private final Function javaBitwiseAndInt;
    private final Function javaBitwiseAndLong;
    private final Function javaBitwiseXOrInt;
    private final Function javaBitwiseXOrLong;
    private final Function javaCastByte;
    private final Function javaCastShort;
    private final Function javaCastInt;
    private final Function javaCastLong;
    private final Function javaCastChar;   
    private final Function lessThan;
    private final Function greaterThan;    
    private final Function greaterOrEquals;
    private final Function lessOrEquals;
    private final Function inByte;
    private final Function inShort;
    private final Function inInt;
    private final Function inLong;
    private final Function inChar;
    private final Function index;
    private final Term one;
    private final Term zero;

    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public IntegerLDT(Services services) {
	super(NAME, services);

        //initialise caches for function symbols from integerHeader.key 
        sharp               = addFunction(services, "#");
        for(int i = 0; i < 10; i++) {
            numberSymbol[i] = addFunction(services, "" + i);
        }
        neglit              = addFunction(services, NEGATIVE_LITERAL_STRING);        
        numbers             = addFunction(services, NUMBERS_NAME.toString());
        assert sharp.sort() == numbers.argSort(0);
        charID              = addFunction(services, CHAR_ID_NAME.toString());
        add                 = addFunction(services, "add");
        neg                 = addFunction(services, "neg");
        sub                 = addFunction(services, "sub");
        mul                 = addFunction(services, "mul");
        div                 = addFunction(services, "div");
        mod                 = addFunction(services, "mod");
        bsum                = addFunction(services, "bsum");
        bprod               = addFunction(services, "bprod");
        jdiv                = addFunction(services, "jdiv");
        jmod                = addFunction(services, "jmod");                  
        unaryMinusJint      = addFunction(services, "unaryMinusJint");
        unaryMinusJlong     = addFunction(services, "unaryMinusJlong");
        addJint             = addFunction(services, "addJint");
        addJlong            = addFunction(services, "addJlong");
        subJint             = addFunction(services, "subJint");
        subJlong            = addFunction(services, "subJlong");
        mulJint             = addFunction(services, "mulJint");
        mulJlong            = addFunction(services, "mulJlong");
        modJint             = addFunction(services, "modJint");
        modJlong            = addFunction(services, "modJlong");
        divJint             = addFunction(services, "divJint");
        divJlong            = addFunction(services, "divJlong");
        shiftrightJint      = addFunction(services, "shiftrightJint");
        shiftrightJlong     = addFunction(services, "shiftrightJlong");
        shiftleftJint       = addFunction(services, "shiftleftJint");
        shiftleftJlong      = addFunction(services, "shiftleftJlong");
        unsignedshiftrightJint  
                            = addFunction(services, "unsignedshiftrightJint");
        unsignedshiftrightJlong 
                            = addFunction(services, "unsignedshiftrightJlong");
        orJint              = addFunction(services, "orJint");
        orJlong             = addFunction(services, "orJlong");
        andJint             = addFunction(services, "andJint");
        andJlong            = addFunction(services, "andJlong");
        xorJint             = addFunction(services, "xorJint");
        xorJlong            = addFunction(services, "xorJlong");
        moduloByte          = addFunction(services, "moduloByte");
        moduloShort         = addFunction(services, "moduloShort");
        moduloInt           = addFunction(services, "moduloInt");
        moduloLong          = addFunction(services, "moduloLong");
        moduloChar          = addFunction(services, "moduloChar");
        javaUnaryMinusInt   = addFunction(services, "javaUnaryMinusInt");
        javaUnaryMinusLong  = addFunction(services, "javaUnaryMinusLong");
        javaBitwiseNegation = addFunction(services, "javaBitwiseNegation");
        javaAddInt          = addFunction(services, "javaAddInt");
        javaAddLong         = addFunction(services, "javaAddLong");
        javaSubInt          = addFunction(services, "javaSubInt");
        javaSubLong         = addFunction(services, "javaSubLong");
        javaMulInt          = addFunction(services, "javaMulInt");
        javaMulLong         = addFunction(services, "javaMulLong");
        javaMod             = addFunction(services, "javaMod");
        javaDivInt          = addFunction(services, "javaDivInt");
        javaDivLong         = addFunction(services, "javaDivLong");
        javaShiftRightInt   = addFunction(services, "javaShiftRightInt");
        javaShiftRightLong  = addFunction(services, "javaShiftRightLong");
        javaShiftLeftInt    = addFunction(services, "javaShiftLeftInt");
        javaShiftLeftLong   = addFunction(services, "javaShiftLeftLong");
        javaUnsignedShiftRightInt 
                            = addFunction(services, "javaUnsignedShiftRightInt");
        javaUnsignedShiftRightLong 
                            = addFunction(services, "javaUnsignedShiftRightLong");
        javaBitwiseOrInt    = addFunction(services, "javaBitwiseOrInt");
        javaBitwiseOrLong   = addFunction(services, "javaBitwiseOrLong");
        javaBitwiseAndInt   = addFunction(services, "javaBitwiseAndInt");
        javaBitwiseAndLong  = addFunction(services, "javaBitwiseAndLong");
        javaBitwiseXOrInt   = addFunction(services, "javaBitwiseXOrInt");
        javaBitwiseXOrLong  = addFunction(services, "javaBitwiseXOrLong");
        javaCastByte        = addFunction(services, "javaCastByte");
        javaCastShort       = addFunction(services, "javaCastShort");
        javaCastInt         = addFunction(services, "javaCastInt");
        javaCastLong        = addFunction(services, "javaCastLong");
        javaCastChar        = addFunction(services, "javaCastChar");
        lessThan            = addFunction(services, "lt");
        greaterThan         = addFunction(services, "gt");
        greaterOrEquals     = addFunction(services, "geq");
        lessOrEquals        = addFunction(services, "leq");
        inByte              = addFunction(services, "inByte");
        inShort             = addFunction(services, "inShort");
        inInt               = addFunction(services, "inInt");
        inLong              = addFunction(services, "inLong");
        inChar              = addFunction(services, "inChar");
        index				= addFunction(services, "index");

        //cache often used constants       
        zero = translateLiteral(new IntLiteral(0), services);
        one = translateLiteral(new IntLiteral(1), services);        
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private boolean isNumberLiteral(Function f) {
        char c = f.name().toString().charAt(0);
        return (c-'0'>=0) && (c-'0'<=9);
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
        
    public Function getNumberTerminator() {
        return sharp;
    }
    
    
    public Function getNumberLiteralFor(int number) {
        if (number < 0 || number > 9) {
            throw new IllegalArgumentException
            ("Number literal symbols range from 0 to 9. Requested was:" + number);
        }
        
        return numberSymbol[number];
    }
    
    
    public Function getNegativeNumberSign() {
        return neglit;
    }    
    
    
    public Function getNumberSymbol() {
        return numbers;
    }
    
    
    public Function getCharSymbol() {
        return charID;
    }
    
    
    public Function getAdd() {
        return add;
    }
    
    
    public Function getNeg() {
        return neg;
    }    
    
    
    public Function getSub() {
        return sub;
    }
    
    
    public Function getMul() {
        return mul;
    }
    
    
    public Function getDiv() {
        return div;
    }
    
    
    public Function getMod() {
        return mod;
    }
    
    
    public Function getBsum() {
	return bsum;
    }    
    
    public Function getBprod() {
    return bprod;
    }
    
    public Function getLessThan() {
        return lessThan;
    }
    
    
    public Function getGreaterThan() {
        return greaterThan;
    }
    
    
    public Function getGreaterOrEquals() {
        return greaterOrEquals;
    }
    
    
    public Function getLessOrEquals() {
        return lessOrEquals;
    }    
    
    /** Placeholder  for the loop index variable in an enhanced for loop over arrays.
     * Follows the proposal by David Cok to adapt JML to Java5.
     * @return
     */
    public Function getIndex(){
    	return index;
    }
    
    
    public Function getInBounds(Type t) {
	if(t == PrimitiveType.JAVA_BYTE) {
	    return inByte;
	} else if(t == PrimitiveType.JAVA_CHAR) {
	    return inChar;
	} else if(t == PrimitiveType.JAVA_INT) {
	    return inInt;
	} else if(t == PrimitiveType.JAVA_LONG) {
	    return inLong;
	} else if(t == PrimitiveType.JAVA_SHORT) {
	    return inShort;
	} else {
	    return null;
	}
    }
    
    
    public Function getJavaCast(Type t) {
	if(t == PrimitiveType.JAVA_BYTE) {
	    return javaCastByte;
	} else if(t == PrimitiveType.JAVA_CHAR) {
	    return javaCastChar;
	} else if(t == PrimitiveType.JAVA_INT) {
	    return javaCastInt;
	} else if(t == PrimitiveType.JAVA_LONG) {
	    return javaCastLong;
	} else if(t == PrimitiveType.JAVA_SHORT) {
	    return javaCastShort;
	} else {
	    return null;
	}
    }
    
    

    /** returns the function symbol for the given operation 
     * null if no function is found for the given operator
     * @return  the function symbol for the given operation 
    */
    @Override
    public Function getFunctionFor(
	    	de.uka.ilkd.key.java.expression.Operator op, 
                Services serv, 
                ExecutionContext ec) {
        final Type opReturnType = op.getKeYJavaType(serv, ec).getJavaType();
        final boolean isLong = opReturnType == PrimitiveType.JAVA_LONG; 
        final boolean isBigint = opReturnType == PrimitiveType.JAVA_BIGINT;

        if (op instanceof GreaterThan) {
            return getGreaterThan();
        } else if (op instanceof GreaterOrEquals) {
            return getGreaterOrEquals();
        } else if (op instanceof LessThan) {
            return getLessThan();
        } else if (op instanceof LessOrEquals) {
            return getLessOrEquals();
        } else if (op instanceof Divide) {
            return isLong ? getJavaDivLong() : (isBigint ? getDiv() : getJavaDivInt());
        } else if (op instanceof Times) {
            return isLong ? getJavaMulLong() : (isBigint ? getMul() : getJavaMulInt());
        } else if (op instanceof Plus) {
            return isLong ? getJavaAddLong() : (isBigint ? getAdd() : getJavaAddInt());
        } else if (op instanceof Minus) {
            return isLong ? getJavaSubLong() : (isBigint ? getSub() : getJavaSubInt());
        } else if (op instanceof Modulo) {
            return isBigint ? getMod() : getJavaMod();
        } else if (op instanceof ShiftLeft) {
            return isLong ? getJavaShiftLeftLong() : getJavaShiftLeftInt();
        } else if (op instanceof ShiftRight) {
            return isLong ? getJavaShiftRightLong() : getJavaShiftRightInt();
        }  else if (op instanceof UnsignedShiftRight) {
            return isLong ? getJavaUnsignedShiftRightLong() 
        	          : getJavaUnsignedShiftRightInt();
        } else if (op instanceof BinaryAnd) {
            return isLong ? getJavaBitwiseAndLong() : getJavaBitwiseAndInt();
        } else if (op instanceof BinaryNot) {
            return getJavaBitwiseNegation();
        } else if (op instanceof BinaryOr) {
            return isLong ? getJavaBitwiseOrLong() : getJavaBitwiseOrInt();
        } else if (op instanceof BinaryXOr) {
            return isLong ? getJavaBitwiseOrLong() : getJavaBitwiseXOrInt();
        } else if (op instanceof Negative) {
            return isLong ? getJavaUnaryMinusLong() : (isBigint ? getNegativeNumberSign() : getJavaUnaryMinusInt());
        } else if (op instanceof TypeCast) {
            return getJavaCast(opReturnType);
        } else {
            return null;
        }
    }
    

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
	                         Term[] subs, 
	                         Services services, 
	                         ExecutionContext ec) {
        if (subs.length == 1) {
            return isResponsible(op, subs[0], services, ec);
        } else if (subs.length == 2) {
            return isResponsible(op, subs[0], subs[1], services, ec); 
        }
        return false;   
    }
    


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
	                         Term left, 
	                         Term right, 
	                         Services services, 
	                         ExecutionContext ec) {
        if(left != null 
           && left.sort().extendsTrans(targetSort()) 
           && right != null 
           && right.sort().extendsTrans(targetSort())) {
            if(getFunctionFor(op, services, ec) != null) {
                return true;
            }
        }
        return false;
    }
    
    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
	                         Term sub, 
	                         Services services, 
	                         ExecutionContext ec) {
        if(sub != null && sub.sort().extendsTrans(targetSort())) {
            if(op instanceof Negative) {
                return true;
            }
        }
        return false;
    }
    


    @Override
    public Term translateLiteral(Literal lit, Services services) {
        int length = 0;
        boolean minusFlag = false;
        Debug.assertTrue(lit instanceof IntLiteral || 
                         lit instanceof LongLiteral ||
                         lit instanceof BigintLiteral ||
                         lit instanceof CharLiteral,
                         "Literal '"+lit+"' is not an integer literal.");

        char[] int_ch=null;
        assert sharp != null;
        Term result = TermBuilder.DF.func(sharp);

        Function identifier=numbers;
        if (lit instanceof CharLiteral) {
            lit = new IntLiteral(""+ (int)(((CharLiteral)lit)
                                           .getCharValue()) ) ;
            identifier = charID;
        }

        String literalString = null;
        if (lit instanceof IntLiteral)
            literalString = ((IntLiteral)lit).getValue();
        else if (lit instanceof LongLiteral)
            literalString = ((LongLiteral)lit).getValue();
        else if (lit instanceof BigintLiteral)
            literalString = ((BigintLiteral)lit).getValue();
        else
            assert false;

        if (literalString.charAt(0) == '-') {
            minusFlag = true;       
            literalString = 
                literalString.substring(1);
        }
        if (lit instanceof IntLiteral) {
            if (literalString.startsWith("0x")) {
                try {
                    int i = Integer.parseInt
                        (literalString.substring(2),16);
                    int_ch=(""+i).toCharArray();
                }catch(NumberFormatException nfe) {
                    Debug.fail("Not a hexadecimal constant!");
                }
            } else {
                int_ch = literalString.toCharArray();
            }            
            length = int_ch.length; 
        } else if (lit instanceof LongLiteral) {
            if (literalString.startsWith("0x")) {
                try {
                    // long literals have an 'L' as last sign; we have
                    // to skip it 
                    final long l = Long.parseLong
                        (literalString.substring(2, 
                                                 literalString.length() - 1), 
                         16);
                    int_ch=(""+l).toCharArray();
                } catch (NumberFormatException nfe) {
                    Debug.fail("Not a hexadecimal constant!");
                }
                length = int_ch.length; 
            } else {
                // long literals have an 'L' as last sign; skip it
                int_ch = literalString.toCharArray();
                length = int_ch.length - 1; 
            }
        }
        
        for (int i = 0; i < length; i++) {
            result = TermBuilder.DF.func(numberSymbol[int_ch[i]-'0'], result);
        }
        if (minusFlag) {
            result = TermBuilder.DF.func(neglit, result);
        }
        result = TermBuilder.DF.func(identifier, result);

        Debug.out("integerldt: result of translating literal (lit, result):", 
                  lit, result);

        return result;
    }
    
    
    @Override
    public boolean hasLiteralFunction(Function f) {
        return containsFunction(f) && (f.arity()==0 || isNumberLiteral(f));
    }
    
    
    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        if(!containsFunction((Function) t.op())) {
            return null;
        }
        Function f = (Function)t.op();
        if(isNumberLiteral(f) || f == numbers || f == charID) {     
            StringBuffer sb = new StringBuffer("");
            Term it = t;
            if (f == charID || f == numbers) {
                it = it.sub(0); 
                f = (Function)it.op();      
            }
            while (isNumberLiteral(f)) {
                sb.insert(0, f.name().toString().charAt(0));
                it=it.sub(0);
                f = (Function)it.op();      
            }
            // numbers must end with a sharp
            if (f == sharp) {
                return new IntLiteral(sb.toString());
            }
        }
        throw new RuntimeException("IntegerLDT: Cannot convert term to program: "
                                   +t);
    }
    
    
    @Override
    public final Type getType(Term t) {
	Operator op = t.op();
	if(op == javaUnaryMinusInt
           || op == javaAddInt
           || op == javaSubInt
           || op == javaMulInt
           || op == javaDivInt
           || op == javaShiftRightInt
           || op == javaShiftLeftInt
           || op == javaUnsignedShiftRightInt
           || op == javaBitwiseOrInt
           || op == javaBitwiseAndInt
           || op == javaBitwiseXOrInt) {
	    return PrimitiveType.JAVA_INT;
	} else if(op == javaUnaryMinusLong
		   || op == javaAddLong
		   || op == javaSubLong
		   || op == javaMulLong
		   || op == javaDivLong
		   || op == javaShiftRightLong
		   || op == javaShiftLeftLong
		   || op == javaUnsignedShiftRightLong
		   || op == javaBitwiseOrLong
		   || op == javaBitwiseAndLong
		   || op == javaBitwiseXOrLong) {
	    return PrimitiveType.JAVA_LONG;
	} else if(op == javaBitwiseNegation || op == javaMod) {
	    return getType(t.sub(0));
	} else if(op == javaCastByte) {
	    return PrimitiveType.JAVA_BYTE;
	} else if(op == javaCastShort) {
	    return PrimitiveType.JAVA_SHORT;
	} else if(op == javaCastInt) {
	    return PrimitiveType.JAVA_INT;
	} else if(op == javaCastLong) {
	    return PrimitiveType.JAVA_LONG;
	} else if(op == javaCastChar) {
	    return PrimitiveType.JAVA_CHAR;
	} else {
   	    assert false : "IntegerLDT: Cannot get Java type for term: " + t;
	    return null;
	}
    }    
    
    
    
    /**
     * returns the function symbol used to represent java-like division of
     * the arithmetical integers
     * @return the function symbol used to represent integer division
     */
    public Function getJDivision() {
        return jdiv;
    }
    
    /**
     * returns the function symbol used to represent the modulo operation of
     * the arithmetical integers
     * @return the function symbol used to represent the integer modulo operation 
     */
    public Function getArithModulo() {        
        return mod;
    }

    /**
     * returns the function symbol used to represent the java-like modulo operation of
     * the arithmetical integers
     * @return the function symbol used to represent the integer modulo operation 
     */
    public Function getJModulo() {        
        return jmod;
    }

    /** returns a function mapping an arithmetic integer to its Java long representation */ 
    public Function getModuloLong() {       
        return modJlong;
    }
    
    /**
     * returns the function symbol interpreted as the Java addition on 
     * int (or promotabel to int) operators, i.e. this addition performs a modulo 
     * operation wrt. to the range of type <code>int</code>. This function is independent 
     * of the chosen integer semantics.
     * 
     * In case you want to represent the Java addition on operands promotable to <code>int</code> 
     * which shall be interpreted by the chosen integer semantics use 
     * {@link IntegerLDT#getJavaAddInt()} instead
     *  
     * @return mathematical interpreted function realising the Java addition on operands of or promotable
     *  to type <code>int</code> 
     */
    public Function getArithJavaIntAddition() {        
        return addJint;
    }
    
   
    /**
     * the function representing the Java operator when one of the
     * operators is an or can be promoted to an int
     * @return function representing the generic Java operator function
     */
    public Function getJavaAddInt() {
        return javaAddInt;
    }


    /**
     * the function representing the Java operator when one of the
     * operators is of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaAddLong() {
        return javaAddLong;
    }

    /**
     * the function representing the Java operator when one of the
     * operators is an or can be promoted to int
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseAndInt() {
        return javaBitwiseAndInt;
    }

    /**
     * the function representing the Java operator when one of the
     * operators is of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseAndLong() {
        return javaBitwiseAndLong;
    }

    /**
     * the function representing the Java operator <code>~</code>
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseNegation() {
        return javaBitwiseNegation;
    }

    /**
     * the function representing the Java operator <code>|</code> 
     * when one of the operands is an or can be promoted to int
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseOrInt() {
        return javaBitwiseOrInt;
    }


    /**
     * the function representing the Java operator <code>|</code> 
     * when one of the operands is of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseOrLong() {
        return javaBitwiseOrLong;
    }

    /**
     * the function representing the Java operator <code>^</code> 
     * when one of the operands is an or can be promoted to int
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseXOrInt() {
        return javaBitwiseXOrInt;
    }


    /**
     * the function representing the Java operator <code>^</code> 
     * when one of the operands is exact of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseXOrLong() {
        return javaBitwiseXOrLong;
    }

    /**
     * the function representing the Java operator <code>(byte)</code> 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastByte() {
        return javaCastByte;
    }

    /**
     * the function representing the Java operator <code>(char)</code> 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastChar() {
        return javaCastChar;
    }


    /**
     * the function representing the Java operator <code>(int)</code> 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastInt() {
        return javaCastInt;
    }

    /**
     * the function representing the Java operator <code>(long)</code> 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastLong() {
        return javaCastLong;
    }

    /**
     * the function representing the Java operator <code>(short)</code> 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastShort() {
        return javaCastShort;
    }

    /**
     * the function representing the Java operator <code>/</code> 
     * when one of the operands is an or a subtype of int
     * @return function representing the generic Java operator function
     */
    public Function getJavaDivInt() {
        return javaDivInt;
    }

    /**
     * the function representing the Java operator <code>/</code> 
     * when one of the operands is exact of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaDivLong() {
        return javaDivLong;
    }


    /**
     * the function representing the Java operator <code>%</code> 
     * when one of the operands is an or a subtype of int
     * @return function representing the generic Java operator function
     */
    public Function getJavaMod() {
        return javaMod;
    }


    /**
     * the function representing the Java operator <code>*</code> 
     * when one of the operands is an or a subtype of int
     * @return function representing the generic Java operator function
     */
    public Function getJavaMulInt() {
        return javaMulInt;
    }


    /**
     * the function representing the Java operator <code>*</code> 
     * when one of the operands is exact of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaMulLong() {
        return javaMulLong;
    }


    /**
     * the function representing the Java operator <code>&lt;&lt;</code> 
     * when one of the operands is an or a subtype of int
     * @return function representing the generic Java operator function
     */
    public Function getJavaShiftLeftInt() {
        return javaShiftLeftInt;
    }


    /**
     * the function representing the Java operator <code>&lt;&lt;</code> 
     * when one of the operands is exact of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaShiftLeftLong() {
        return javaShiftLeftLong;
    }


    /**
     * the function representing the Java operator <code>&gt;&gt;</code> 
     * when one of the operands is an or a subtype of int
     * @return function representing the generic Java operator function
     */
    public Function getJavaShiftRightInt() {
        return javaShiftRightInt;
    }

    /**
     * the function representing the Java operator <code>&gt;&gt;</code> 
     * when one of the operands is exact of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaShiftRightLong() {
        return javaShiftRightLong;
    }

    /**
     * the function representing the Java operator <code>-</code> 
     * when one of the operands is an or a subtype of int
     * @return function representing the generic Java operator function
     */
    public Function getJavaSubInt() {
        return javaSubInt;
    }

    /**
     * the function representing the Java operator <code>-</code> 
     * when one of the operands is exact of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaSubLong() {
        return javaSubLong;
    }


    /**
     * the function representing the Java operator <code>-expr</code> 
     * when one of the operands is an or a subtype of int
     * @return function representing the generic Java operator function
     */
    public Function getJavaUnaryMinusInt() {
        return javaUnaryMinusInt;
    }

    /**
     * the function representing the Java operator <code>-exprLong</code> 
     * when one of the operands is exact of type long
     * @return function representing the generic Java operator function
     */
    public Function getJavaUnaryMinusLong() {
        return javaUnaryMinusLong;
    }


    /**
     * the function representing the Java operator <code>&gt;&gt;&gt;</code> 
     * when one of the operands is an or a subtype of int
     * @return function representing the generic Java operator function
     */    
    public Function getJavaUnsignedShiftRightInt() {
        return javaUnsignedShiftRightInt;
    }


    /**
     * the function representing the Java operator <code>&gt;&gt;&gt;</code> 
     * when one of the operands is exact of type long
     * @return function representing the generic Java operator function
     */    
    public Function getJavaUnsignedShiftRightLong() {
        return javaUnsignedShiftRightLong;
    }
    
    public Term zero() {	
	return zero;
    }

    public Term one() {	
	return one;
    }
} 
