// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.abstraction;

import java.util.HashMap;

import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.logic.ProgramElementName;

/**
   A program model element representing primitive types.
   @author AL
   @author RN
 */
public class PrimitiveType
    implements Type {

    public static final PrimitiveType JAVA_BYTE  = 
	new PrimitiveType("byte", new IntLiteral(0));
    public static final PrimitiveType JAVA_SHORT = 
	new PrimitiveType("short", new IntLiteral(0));
    public static final PrimitiveType JAVA_INT = 
	new PrimitiveType("int", new IntLiteral(0));
    public static final PrimitiveType JAVA_CHAR = 
	new PrimitiveType("char", new CharLiteral('\u0000'));
    public static final PrimitiveType JAVA_LONG  = 
	new PrimitiveType("long", new LongLiteral(0L));
    public static final PrimitiveType JAVA_FLOAT = 
	new PrimitiveType("float", new FloatLiteral(0.0f));
    public static final PrimitiveType JAVA_DOUBLE  = 
	new PrimitiveType("double", new DoubleLiteral(0.0d));
    public static final PrimitiveType JAVA_BOOLEAN = 
	new PrimitiveType("boolean", BooleanLiteral.FALSE);
    public static final PrimitiveType JAVA_SET = 
	new PrimitiveType("\\locset", EmptySetLiteral.INSTANCE);
    public static final PrimitiveType PROGRAM_SV   = new PrimitiveType("SV", null);

    private ProgramElementName arrayElementName = null;

    private static final HashMap<String,PrimitiveType> typeMap = 
        new HashMap<String, PrimitiveType>(); 
    static {
	typeMap.put("byte", JAVA_BYTE);
	typeMap.put("short", JAVA_SHORT);
	typeMap.put("int", JAVA_INT);
	typeMap.put("char", JAVA_CHAR);
	typeMap.put("long", JAVA_LONG);
	typeMap.put("float", JAVA_FLOAT);
	typeMap.put("double", JAVA_DOUBLE);
	typeMap.put("boolean", JAVA_BOOLEAN);	
	typeMap.put("\\locset", JAVA_SET);
    }

    public static PrimitiveType getPrimitiveType(String name) {
	return typeMap.get(name);
    }



    private final String name;
    private final Literal defaultValue;

    private PrimitiveType(String name, Literal defaultValue) {
	this.defaultValue = defaultValue;
	this.name = name.intern();
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
	}
	assert arrayElementName != null;
	return arrayElementName;
    }

}
