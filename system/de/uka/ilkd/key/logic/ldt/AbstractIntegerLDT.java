// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.hoare.init.HoareProfile;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.LongLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;


/** 
 * This class inherits from LDT and implements all method that are
 * necessary to handle integers, shorts and bytes. It caches the symbols 
 * declared in integerHeader.key and offers methods to convert java
 * number types to their logic counterpart.
 */
public abstract class AbstractIntegerLDT extends LDT {

    //public name constants
    public static final String NEGATIVE_LITERAL_STRING = "neglit";
    public static final Name NUMBERS_NAME = new Name("Z");
    public static final Name CHAR_ID_NAME = new Name("C"); 
    
    //the following fields cache the symbols from integerHeader.key. 
    //(explanations see there)
    protected final Function sharp;
    protected final Function numberSymbol[] = new Function[10];
    protected final Function numbers;
    protected final Function negativeNumber;
    protected final Function charID;
    protected final Function plus;
    protected final Function negative;
    protected final Function minus;
    protected final Function times;
    protected final Function divide;
    protected final Function modulo;
    protected final Function jDivide;
    protected final Function jModulo;
    protected final Function unaryMinusJint;
    protected final Function unaryMinusJlong;
    protected final Function addJint;
    protected final Function addJlong;
    protected final Function subJint;
    protected final Function subJlong;
    protected final Function mulJint;
    protected final Function mulJlong;
    protected final Function modJint;
    protected final Function modJlong;
    protected final Function divJint;
    protected final Function divJlong;
    protected final Function shiftrightJint;
    protected final Function shiftrightJlong;
    protected final Function shiftleftJint;
    protected final Function shiftleftJlong;
    protected final Function unsignedshiftrightJint;
    protected final Function unsignedshiftrightJlong;
    protected final Function orJint;
    protected final Function orJlong;
    protected final Function andJint;
    protected final Function andJlong;
    protected final Function xorJint;
    protected final Function xorJlong;
    protected final Function moduloByte;
    protected final Function moduloShort;
    protected final Function moduloInt;
    protected final Function moduloLong;
    protected final Function moduloChar;
    protected final Function javaUnaryMinusInt;
    protected final Function javaUnaryMinusLong;
    protected final Function javaBitwiseNegation;
    protected final Function javaAddInt;
    protected final Function javaAddLong;
    protected final Function javaSubInt;
    protected final Function javaSubLong;
    protected final Function javaMulInt;    
    protected final Function javaMulLong;
    protected final Function javaMod;
    protected final Function javaDivInt;
    protected final Function javaDivLong;
    protected final Function javaShiftRightInt;
    protected final Function javaShiftRightLong;
    protected final Function javaShiftLeftInt;
    protected final Function javaShiftLeftLong;
    protected final Function javaUnsignedShiftRightInt;
    protected final Function javaUnsignedShiftRightLong;
    protected final Function javaBitwiseOrInt;
    protected final Function javaBitwiseOrLong;
    protected final Function javaBitwiseAndInt;
    protected final Function javaBitwiseAndLong;
    protected final Function javaBitwiseXOrInt;
    protected final Function javaBitwiseXOrLong;
    protected final Function javaCastByte;
    protected final Function javaCastShort;
    protected final Function javaCastInt;
    protected final Function javaCastLong;
    protected final Function javaCastChar;   
    protected final Function lessThan;
    protected final Function greaterThan;    
    protected final Function greaterOrEquals;
    protected final Function lessOrEquals;
    protected final Function inByte;
    protected final Function inShort;
    protected final Function inInt;
    protected final Function inLong;
    protected final Function inChar;

    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    protected AbstractIntegerLDT(Name name, 
	    			 Namespace sorts, 
	    			 Namespace functions, 
	    			 Type javaType) {
	super(name, sorts, javaType);

        //initialise caches for function symbols from integerHeader.key 
        sharp               = addFunction(functions, "#");
        for (int i = 0; i < 10; i++) {
            numberSymbol[i] = addFunction(functions, ""+i);
        }        
        numbers             = addFunction(functions, NUMBERS_NAME.toString());
        assert sharp.sort() == numbers.argSort(0);
        negativeNumber      = addFunction(functions, NEGATIVE_LITERAL_STRING);
        charID              = addFunction(functions, CHAR_ID_NAME.toString());
        plus                = addFunction(functions, "add");
        negative            = addFunction(functions, "neg");
        minus               = addFunction(functions, "sub");
        times               = addFunction(functions, "mul");
        divide              = addFunction(functions, "div");
        modulo              = addFunction(functions, "mod");
        jDivide             = addFunction(functions, "jdiv");
        jModulo             = addFunction(functions, "jmod");                  
        unaryMinusJint      = addFunction(functions, "unaryMinusJint");
        unaryMinusJlong     = addFunction(functions, "unaryMinusJlong");
        addJint             = addFunction(functions, "addJint");
        addJlong            = addFunction(functions, "addJlong");
        subJint             = addFunction(functions, "subJint");
        subJlong            = addFunction(functions, "subJlong");
        mulJint             = addFunction(functions, "mulJint");
        mulJlong            = addFunction(functions, "mulJlong");
        modJint             = addFunction(functions, "modJint");
        modJlong            = addFunction(functions, "modJlong");
        divJint             = addFunction(functions, "divJint");
        divJlong            = addFunction(functions, "divJlong");
        shiftrightJint      = addFunction(functions, "shiftrightJint");
        shiftrightJlong     = addFunction(functions, "shiftrightJlong");
        shiftleftJint       = addFunction(functions, "shiftleftJint");
        shiftleftJlong      = addFunction(functions, "shiftleftJlong");
        unsignedshiftrightJint  
                            = addFunction(functions, "unsignedshiftrightJint");
        unsignedshiftrightJlong 
                            = addFunction(functions, "unsignedshiftrightJlong");
        orJint              = addFunction(functions, "orJint");
        orJlong             = addFunction(functions, "orJlong");
        andJint             = addFunction(functions, "andJint");
        andJlong            = addFunction(functions, "andJlong");
        xorJint             = addFunction(functions, "xorJint");
        xorJlong            = addFunction(functions, "xorJlong");
        moduloByte          = addFunction(functions, "moduloByte");
        moduloShort         = addFunction(functions, "moduloShort");
        moduloInt           = addFunction(functions, "moduloInt");
        moduloLong          = addFunction(functions, "moduloLong");
        moduloChar          = addFunction(functions, "moduloChar");
        javaUnaryMinusInt   = addFunction(functions, "javaUnaryMinusInt");
        javaUnaryMinusLong  = addFunction(functions, "javaUnaryMinusLong");
        javaBitwiseNegation = addFunction(functions, "javaBitwiseNegation");
        javaAddInt          = addFunction(functions, "javaAddInt");
        javaAddLong         = addFunction(functions, "javaAddLong");
        javaSubInt          = addFunction(functions, "javaSubInt");
        javaSubLong         = addFunction(functions, "javaSubLong");
        javaMulInt          = addFunction(functions, "javaMulInt");
        javaMulLong         = addFunction(functions, "javaMulLong");
        javaMod             = addFunction(functions, "javaMod");
        javaDivInt          = addFunction(functions, "javaDivInt");
        javaDivLong         = addFunction(functions, "javaDivLong");
        javaShiftRightInt   = addFunction(functions, "javaShiftRightInt");
        javaShiftRightLong  = addFunction(functions, "javaShiftRightLong");
        javaShiftLeftInt    = addFunction(functions, "javaShiftLeftInt");
        javaShiftLeftLong   = addFunction(functions, "javaShiftLeftLong");
        javaUnsignedShiftRightInt 
                            = addFunction(functions, "javaUnsignedShiftRightInt");
        javaUnsignedShiftRightLong 
                            = addFunction(functions, "javaUnsignedShiftRightLong");
        javaBitwiseOrInt    = addFunction(functions, "javaBitwiseOrInt");
        javaBitwiseOrLong   = addFunction(functions, "javaBitwiseOrLong");
        javaBitwiseAndInt   = addFunction(functions, "javaBitwiseAndInt");
        javaBitwiseAndLong  = addFunction(functions, "javaBitwiseAndLong");
        javaBitwiseXOrInt   = addFunction(functions, "javaBitwiseXOrInt");
        javaBitwiseXOrLong  = addFunction(functions, "javaBitwiseXOrLong");
        javaCastByte        = addFunction(functions, "javaCastByte");
        javaCastShort       = addFunction(functions, "javaCastShort");
        javaCastInt         = addFunction(functions, "javaCastInt");
        javaCastLong        = addFunction(functions, "javaCastLong");
        javaCastChar        = addFunction(functions, "javaCastChar");
        lessThan            = addFunction(functions, "lt");
        greaterThan         = addFunction(functions, "gt");
        greaterOrEquals     = addFunction(functions, "geq");
        lessOrEquals        = addFunction(functions, "leq");
        inByte              = addFunction(functions, "inByte");
        inShort             = addFunction(functions, "inShort");
        inInt               = addFunction(functions, "inInt");
        inLong              = addFunction(functions, "inLong");
        inChar              = addFunction(functions, "inChar");
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private boolean isNumberLiteral(Function f) {
        char c=f.name().toString().charAt(0);
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
    
    
    public Function getNumberSymbol() {
        return numbers;
    }
    
    
    public Function getNegativeNumberSign() {
        return negativeNumber;
    }
    
    
    public Function getCharSymbol() {
        return charID;
    }
    
    
    public abstract Function getAdd();
    
    
    public Function getNeg() {
        return negative;
    }

    
    public abstract Function getSub();
    
    
    public abstract Function getMul();
    
    
    public abstract Function getDiv();
    
    
    public abstract Function getMod();
    
    public abstract Function getShiftLeft();    
    
    public abstract Function getShiftRight();
    
        
    public abstract Function getUnsignedShiftRight();
    
    
    public abstract Function getBitwiseOr();
    
    
    public abstract Function getBitwiseAnd();
    
    
    public abstract Function getBitwiseXor();
    
    
    public abstract Function getBitwiseNegation();
    
    
    public abstract Function getCast();
    
    
    public abstract Function getLessThan();
    
    
    public abstract Function getGreaterThan();
    
    
    public abstract Function getGreaterOrEquals();
    
    
    public abstract Function getLessOrEquals();
    
    
    public abstract Function getInBounds();    
    

    /** returns the function symbol for the given operation 
     * null if no function is found for the given operator
     * @return  the function symbol for the given operation 
    */
    public Function getFunctionFor
        (de.uka.ilkd.key.java.expression.Operator op, 
                Services serv, ExecutionContext ec) {
        final KeYJavaType opReturnType;
        if (ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof HoareProfile) {
            opReturnType = serv.getJavaInfo().getPrimitiveKeYJavaType("int");
        } else {
            opReturnType = op.getKeYJavaType(serv, ec);
        }

        if (op instanceof GreaterThan) {
            return greaterThan;
        } else if (op instanceof GreaterOrEquals) {
            return greaterOrEquals;
        } else if (op instanceof LessThan) {
            return lessThan;
        } else if (op instanceof LessOrEquals) {
            return lessOrEquals;
        } else if (op instanceof Divide) {                      
            return 
                opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
                ? getJavaDivLong() : getJavaDivInt();
        } else if (op instanceof Times) {
            return 
            opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaMulLong() : getJavaMulInt();
        } else if (op instanceof Plus) {
            return 
            opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaAddLong() : getJavaAddInt();
        } else if (op instanceof Minus) {
            return 
            opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaSubLong() : getJavaSubInt();
        } else if (op instanceof Modulo) {
            return getJavaMod();
        } else if (op instanceof ShiftLeft) {
            return 
                opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
                ? getJavaShiftLeftLong() : getJavaShiftLeftInt();
        } else if (op instanceof ShiftRight) {
            return opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaShiftRightLong() : getJavaShiftRightInt();
        }  else if (op instanceof UnsignedShiftRight) {
            return opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaUnsignedShiftRightLong() : getJavaUnsignedShiftRightInt();
        } else if (op instanceof BinaryAnd) {
            assert opReturnType.getJavaType() != PrimitiveType.JAVA_BOOLEAN;
            return opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaBitwiseAndLong() : getJavaBitwiseAndInt();
        } else if (op instanceof BinaryNot) {
            assert opReturnType.getJavaType() != PrimitiveType.JAVA_BOOLEAN;
            return getJavaBitwiseNegation();
        } else if (op instanceof BinaryOr) {
            assert opReturnType.getJavaType() != PrimitiveType.JAVA_BOOLEAN;
            return opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaBitwiseOrLong() : getJavaBitwiseOrInt();
        } else if (op instanceof BinaryXOr) {
            assert opReturnType.getJavaType() != PrimitiveType.JAVA_BOOLEAN;
            return opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaBitwiseOrLong() : getJavaBitwiseOrInt();
        } else if (op instanceof Negative) {
            return opReturnType.getJavaType() == PrimitiveType.JAVA_LONG 
            ? getJavaUnaryMinusLong() : getJavaUnaryMinusLong();
        } else if (op instanceof TypeCast) {
            if (opReturnType.getJavaType() == PrimitiveType.JAVA_CHAR) {
                return getJavaCastChar();
            } else if (opReturnType.getJavaType() == PrimitiveType.JAVA_BYTE) {
                return getJavaCastByte();
            } else if (opReturnType.getJavaType() == PrimitiveType.JAVA_SHORT) {
                return getJavaCastShort();
            } else if (opReturnType.getJavaType() == PrimitiveType.JAVA_INT) {
                return getJavaCastInt();
            } else if (opReturnType.getJavaType() == PrimitiveType.JAVA_LONG) {
                return getJavaCastLong();
            }  
        }
        return null;
//final KeYJavaType opReturnType = op.getKeYJavaType(serv, ec);
/*
        if (op instanceof GreaterThan) {
            return getGreaterThan();
        } else if (op instanceof GreaterOrEquals) {
            return getGreaterOrEquals();
        } else if (op instanceof LessThan) {
            return getLessThan();
        } else if (op instanceof LessOrEquals) {
            return getLessOrEquals();
        } else if (op instanceof Divide) {                      
            return getDiv();
        } else if (op instanceof Times) {
            return getMul();
        } else if (op instanceof Plus) {
            return getAdd();
        } else if (op instanceof Minus) {
            return getSub(); 
        } else if (op instanceof Modulo) {
            return getMod();
        } else if (op instanceof ShiftLeft) {
            return getShiftLeft();
        } else if (op instanceof ShiftRight) {
            return getShiftRight();
        }  else if (op instanceof UnsignedShiftRight) {
            return getUnsignedShiftRight();
        } else if (op instanceof BinaryAnd) {
            return getBitwiseAnd();
        } else if (op instanceof BinaryNot) {
            return getBitwiseNegation();
        } else if (op instanceof BinaryOr) {
            return getBitwiseOr();
        } else if (op instanceof BinaryXOr) {
            return getBitwiseXor();
        } else if (op instanceof Negative) {
            return getNeg();
        } else if (op instanceof TypeCast) {
            return getCast();
        } else {
            return null;
        }*/
    }
    
    
    /** returns true if the LDT offers an operation for the given java
     * operator and the logic subterms 
     * @param op the de.uka.ilkd.key.java.expression.Operator to
     * translate
     * @param subs the logic subterms of the java operator
     * @return  true if the LDT offers an operation for the given java
     * operator and the subterms 
     */
    public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
        if (subs.length == 1) {
            return isResponsible(op, subs[0], services, ec);
        } else if (subs.length == 2) {
            return isResponsible(op, subs[0], subs[1], services, ec); 
        }
        return false;   
    }
    

    /** returns true if the LDT offers an operation for the given
     * binary java operator and the logic subterms 
     * @param op the de.uka.ilkd.key.java.expression.Operator to
     * translate
     * @param left the left subterm of the java operator
     * @param right the right subterm of the java operator
     * @return  true if the LDT offers an operation for the given java
     * operator and the subterms 
     */
    public boolean isResponsible(Operator op, Term left, Term right, 
            Services services, ExecutionContext ec) {
        
        if (left!=null && left.sort().extendsTrans(targetSort()) 
                && right!=null && right.sort().extendsTrans(targetSort())) {
            if (getFunctionFor(op, services, ec) != null) {
                return true;
            }
        }
        return false;
    }
    
    
    /** returns true if the LDT offers an operation for the given
     * unary java operator and the logic subterms 
     * @param op the de.uka.ilkd.key.java.expression.Operator to
     * translate
     * @param sub the logic subterms of the java operator
     * @return  true if the LDT offers an operation for the given java
     * operator and the subterm
     */
    public boolean isResponsible(Operator op, Term sub, Services services, ExecutionContext ec) {
        if (sub != null && sub.sort().extendsTrans(targetSort())) {
            if (op instanceof Negative) {
                return true;
            }
        }
        return false;
    }
    

    /** translates a given integer literal to its logic counterpart 
     * @param lit the Literal to be translated (has to be an
     * IntLiteral of an LongLiteral
     * @result the Term that represent the given integer in its logic
     * form
     */ 
    public Term translateLiteral(Literal lit) {
        int length=0;
        boolean minusFlag = false;
        Debug.assertTrue(lit instanceof IntLiteral || 
                         lit instanceof LongLiteral ||
                         lit instanceof CharLiteral,
                         "Literal '"+lit+"' is not an integer literal.");

        char[] int_ch=null;
        assert sharp != null;
        Term result = TermFactory.DEFAULT.createFunctionTerm(sharp);

        Function identifier=numbers;
        if (lit instanceof CharLiteral) {
            lit = new IntLiteral(""+ (int)(((CharLiteral)lit)
                                           .getCharValue()) ) ;
            identifier = charID;
        }

        String literalString = ""; 
        if (lit instanceof IntLiteral) {
            literalString = ((IntLiteral)lit).getValue();
        } else {
            Debug.assertTrue(lit instanceof LongLiteral);
            literalString = ((LongLiteral)lit).getValue();
        }

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
            result = TermFactory.DEFAULT.createFunctionTerm
                (numberSymbol[int_ch[i]-'0'], result);
        }
        if (minusFlag) {
            result = TermFactory.DEFAULT.createFunctionTerm
                (negativeNumber, result);
        }
        result = TermFactory.DEFAULT.createFunctionTerm
            (identifier, result);

        Debug.out("integerldt: result of translating literal (lit, result):", 
                  lit, result);

        return result;
    }
    
    
    public boolean hasLiteralFunction(Function f) {
        return containsFunction(f) && (f.arity()==0 || isNumberLiteral(f));
    }
    

    public Expression translateTerm(Term t, ExtList children) {
        if (!containsFunction((Function) t.op())) return null;
        Function f = (Function)t.op();
        if (isNumberLiteral(f) || f == numbers || f ==charID) {     
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
        throw new RuntimeException("AbstractIntegerLDT: Cannot convert term to program: "
                                   +t);
    }
    
    
    /**
     * returns the function symbol used to represent java-like division of
     * the arithmetical integers
     * @return the function symbol used to represent integer division
     */
    public Function getJDivision() {
        return jDivide;
    }
    
    /**
     * returns the function symbol used to represent the modulo operation of
     * the arithmetical integers
     * @return the function symbol used to represent the integer modulo operation 
     */
    public Function getArithModulo() {        
        return modulo;
    }

    /**
     * returns the function symbol used to represent the java-like modulo operation of
     * the arithmetical integers
     * @return the function symbol used to represent the integer modulo operation 
     */
    public Function getJModulo() {        
        return jModulo;
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
     * {@link AbstractIntegerLDT#getJavaAddInt()} instead
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
} 
