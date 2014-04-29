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

package de.uka.ilkd.key.java.abstraction;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.BigintLiteral;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.DoubleLiteral;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.literal.EmptySetLiteral;
import de.uka.ilkd.key.java.expression.literal.FloatLiteral;
import de.uka.ilkd.key.java.expression.literal.FreeLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.LongLiteral;
import de.uka.ilkd.key.java.expression.literal.RealLiteral;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.ldt.FreeLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.RealLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;

/**
   A program model element representing primitive types.
   @author AL
   @author RN
 */
public final class PrimitiveType implements Type {

    // must be first in file.
    private static final Map<String,PrimitiveType> typeMap = 
            new LinkedHashMap<String, PrimitiveType>(); 
    // must be first in file.
    private static final Map<Name,PrimitiveType> ldtMap = 
            new LinkedHashMap<Name, PrimitiveType>(); 

    public static final PrimitiveType JAVA_BYTE  =
	new PrimitiveType("byte", new IntLiteral(0), IntegerLDT.NAME);
    public static final PrimitiveType JAVA_SHORT =
	new PrimitiveType("short", new IntLiteral(0), IntegerLDT.NAME);
    public static final PrimitiveType JAVA_INT =
	new PrimitiveType("int", new IntLiteral(0), IntegerLDT.NAME);
    public static final PrimitiveType JAVA_CHAR =
	new PrimitiveType("char", new CharLiteral('\u0000'), IntegerLDT.NAME);
    public static final PrimitiveType JAVA_LONG  =
	new PrimitiveType("long", new LongLiteral(0L), IntegerLDT.NAME);
    public static final PrimitiveType JAVA_BIGINT =
            new PrimitiveType("\\bigint", new BigintLiteral(0), IntegerLDT.NAME);
    public static final PrimitiveType JAVA_FLOAT =
	new PrimitiveType("float", new FloatLiteral(0.0f), FloatLDT.NAME);
    public static final PrimitiveType JAVA_DOUBLE  =
	new PrimitiveType("double", new DoubleLiteral(0.0d), DoubleLDT.NAME);
    public static final PrimitiveType JAVA_REAL =
            new PrimitiveType("\\real", new RealLiteral(), RealLDT.NAME);
    public static final PrimitiveType JAVA_BOOLEAN =
	new PrimitiveType("boolean", BooleanLiteral.FALSE, BooleanLDT.NAME);
    public static final PrimitiveType JAVA_LOCSET =
	new PrimitiveType("\\locset", EmptySetLiteral.LOCSET, LocSetLDT.NAME);
    public static final PrimitiveType JAVA_SEQ =
	new PrimitiveType("\\seq", EmptySeqLiteral.INSTANCE, SeqLDT.NAME);
    public static final PrimitiveType JAVA_FREE_ADT =
            new PrimitiveType("\\free", FreeLiteral.INSTANCE, FreeLDT.NAME);

    public static final PrimitiveType PROGRAM_SV   = new PrimitiveType("SV", null, null);

    private ProgramElementName arrayElementName = null;


    public static PrimitiveType getPrimitiveType(String name) {
	return typeMap.get(name);
    }

    public static PrimitiveType getPrimitiveTypeByLDT(Name ldtName) {
        return ldtMap.get(ldtName);
    }

    private final String name;
    private final Literal defaultValue;
    private Name ldtName;

    private PrimitiveType(String name, Literal defaultValue, Name ldtName) {
	this.defaultValue = defaultValue;
	this.name = name.intern();
	this.ldtName = ldtName;
	typeMap.put(name, this);

	if(ldtName != null) {
	    ldtMap.put(ldtName, this);
	}
    }

    /**
       Returns the name of this type.
       @return the name of this type.
     */
    public String getName() {
	return name;
    }

    public boolean equals(Object o) {
	if (o instanceof PrimitiveType &&
	    ((PrimitiveType)o).getName().equals(name)) {
		return true;
	}
	return false;
    }

    public int hashCode() {
	return getName().hashCode();
    }

    /**
     * returns the default value of the given type
     * according to JLS ???4.5.5
     * <em>ATTENTION:</em> usually for byte and short this should be (byte) 0
     * (rsp. (short)0) but currently is just 0.
     * @return the default value of the given type
     * according to JLS ???4.5.5
     */
    public Literal getDefaultValue() {
	return defaultValue;
    }

    /**
       Returns the name of type.
       @return the full name of this program model element.
     */
    public String getFullName() {
	return name;
    }

    /**
       Returns the name of type.
       @return the full name of this program model element.
     */
    public String toString() {
	return name;
    }


    /**
       Returns the specific name of this primitive type used
       in array types.
     */
    public ProgramElementName getArrayElementName() {
	if (arrayElementName == null) {
	    if (this.getName().equals("byte"))
	        arrayElementName = new ProgramElementName("[B");
	    else if (this.getName().equals("char"))
		arrayElementName = new ProgramElementName("[C");
	    else if (this.getName().equals("double"))
		arrayElementName = new ProgramElementName("[D");
	    else if (this.getName().equals("float"))
		arrayElementName =  new ProgramElementName("[F");
	    else if (this.getName().equals("int"))
		arrayElementName = new ProgramElementName("[I");
	    else if (this.getName().equals("long"))
		arrayElementName = new ProgramElementName("[J");
	    else if (this.getName().equals("short"))
		arrayElementName = new ProgramElementName("[S");
	    else if (this.getName().equals("boolean"))
		arrayElementName = new ProgramElementName("[Z");
	    else if (this.getName().equals("\\locset"))
		arrayElementName = new ProgramElementName("[X");
	    else if (this.getName().equals("\\bigint"))
	        arrayElementName = new ProgramElementName("[Y");
        else if (this.getName().equals("\\real"))
            arrayElementName = new ProgramElementName("[R");
	}
	assert arrayElementName != null;
	return arrayElementName;
    }

    /**
     * Returns whether this is a Java type which translates to int in DL.
     */
    public boolean isIntegerType () {
        return this == JAVA_BYTE
            || this == JAVA_CHAR
            || this == JAVA_SHORT
            || this == JAVA_INT
            || this == JAVA_LONG
            || this == JAVA_BIGINT;
    }

    /**
     * Returns true if this is an integer or floating point type.
     */
    public boolean isArithmeticType () {
        return isIntegerType()
            || this == JAVA_FLOAT
            || this == JAVA_DOUBLE
            || this == JAVA_REAL;
    }

    /**
     * Gets the name of the LDT corresponding to this primitive type.
     *
     * @return may be null if no name set
     */
    public Name getCorrespondingLDTName() {
        return ldtName;
    }

}