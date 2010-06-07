// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.io.StringWriter;
import java.util.HashSet;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.SyntacticalProgramVariable;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.SyntacticalTypeRef;
import de.uka.ilkd.key.util.ExtList;

/**
 * @author mbender
 * 
 */
public class AccessMethodsManager {

    private static AccessMethodsManager instance = null;

    private final ReflectionClassCreator fc;

    public static final String NAME_OF_CLASS = "RFL";

    private static final String ARRAY = "_ARRAY_";

    // setter and getter methods will be created for these types.
    private static final String[] PRIMITIVE_TYPES = { "int", "long", "byte",
	    "char", "boolean", "float", "double" };

    // Default values for primitive types
    private static final String[] PRIM_TYP_DEF_VAL = { "0", "0", "0", "' '",
	    "false", "0", "0" };

    private final ReferencePrefix twClass;

    private HashSet<Sort> usedObjectSorts;

    private AccessMethodsManager() {
	fc = new ReflectionClassCreator();
	twClass = new SyntacticalTypeRef(new ProgramElementName(NAME_OF_CLASS));
	init();
    }

    public void init() {
	usedObjectSorts = new HashSet<Sort>();
    }

    /**
     * Following the singleton pattern this method returns the instance of this
     * class
     * 
     * @return the instance
     */
    public static AccessMethodsManager getInstance() {
	if (instance == null) {
	    instance = new AccessMethodsManager();
	}
	return instance;
    }

    /**
     * @return String representing the ReflectionClass
     */
    public StringWriter createClass() {
	return fc.createClass();
    }

    // ********************
    // ********************
    //    
    // Calls to create new Objects
    //    
    // ********************
    // ********************

    /**
     * @param rhs
     *            the 'old' New-statement
     * @return a method reference to call the approrpiate new-method
     */
    public MethodReference callNew(final New rhs) {
	final Sort sort = ((TypeRef) rhs.getTypeReference()).getKeYJavaType()
	        .getSort();
	usedObjectSorts.add(sort);
	return new MethodReference(new ImmutableArray<Expression>(),
	        new ProgramElementName("new" + clean(sort.toString())), twClass);
    }

    /**
     * @param rhs
     *            the 'old' NewArray-statement
     * @return a method reference to call the approrpiate new-method
     */
    public MethodReference callNew(final NewArray rhs) {
	final Sort sort = rhs.getKeYJavaType().getSort();
	usedObjectSorts.add(sort);
	return new MethodReference(rhs.getArguments(), new ProgramElementName(
	        "new" + clean(sort.toString())), twClass);
    }

    // ********************
    // ********************
    //    
    // Calls to set values
    //    
    // ********************
    // ********************

    /**
     * @param lhs
     *            the left hand site of a assignment
     * @param rhs
     *            the right hand site of a assignment
     * @return a methodreference to set the location to the given value
     */
    public MethodReference callSetter(final FieldReference lhs,
	    final Expression rhs) {
	final ProgramVariable pv = lhs.getProgramVariable();
	final StringLiteral var = new StringLiteral(varName(pv));
	final Expression paraClassClass = classParam(pv);
	final Expression paraClassObj = objParam(lhs.getReferencePrefix(), pv);
	final Sort sort = pv.sort();
	usedObjectSorts.add(sort);
	return new MethodReference(new ImmutableArray<Expression>(
	        paraClassClass, paraClassObj, var, rhs),
	        new ProgramElementName("_set_" + clean(sort.toString())),
	        twClass);
    }

    /**
     * @param lhs
     *            the left hand site of a assignment
     * @param rhs
     *            rhs the right hand site of a assignment
     * @returna methodreference to set the location to the given value
     */
    public Statement callSetter(final ArrayReference lhs, final Expression rhs) {
	final ReferencePrefix refPre = lhs.getReferencePrefix();
	if (refPre instanceof LocationVariable) {
	    return new CopyAssignment(lhs, rhs);
	} else if (refPre instanceof FieldReference) {
	    final ReferencePrefix reference = callGetter((FieldReference) refPre);
	    final Expression[] index = { lhs.getExpressionAt(lhs
		    .getExpressionCount() - 1) };
	    return new CopyAssignment(new ArrayReference(reference, index), rhs);
	}
	throw new RuntimeException("Missing type for refPre=\n" + refPre
	        + " with class: " + refPre.getClass());
    }

    // ********************
    // ********************
    //    
    // Calls to get values
    //    
    // ********************
    // ********************

    /**
     * @param lhs
     *            the location to get
     * @return a methodreference to get the location
     */
    public MethodReference callGetter(final FieldReference lhs) {
	final ProgramVariable pv = lhs.getProgramVariable();
	final StringLiteral var = new StringLiteral(varName(pv));
	final Expression paraClassClass = classParam(pv);
	final Expression paraClassObj = objParam(lhs.getReferencePrefix(), pv);
	final Sort sort = pv.sort();
	usedObjectSorts.add(sort);
	return new MethodReference(new ImmutableArray<Expression>(
	        paraClassClass, paraClassObj, var), new ProgramElementName(
	        "_get_" + clean(sort.toString())), twClass);
    }

    @SuppressWarnings("unchecked")
    public ArrayLengthReference arrayLength(final FieldReference fr) {
	final ExtList l = new ExtList();
	l.add(objParam(fr.getReferencePrefix(), fr
	        .getProgramVariable()));
	return new ArrayLengthReference(l);
    }

    /**
     * @param lhs
     *            lhs the location to get
     * @return a methodreference to get the location
     */
    public Expression callGetter(final ArrayReference lhs) {
	final ReferencePrefix refPre = lhs.getReferencePrefix();
	if (refPre instanceof LocationVariable) {
	    return lhs;
	} else if (refPre instanceof FieldReference) {
	    final ReferencePrefix reference = callGetter((FieldReference) refPre);
	    final Expression[] index = { lhs.getExpressionAt(lhs
		    .getExpressionCount() - 1) };
	    return new ArrayReference(reference, index);
	} else if (refPre instanceof MethodReference){
	    return lhs;
	}
	throw new RuntimeException("Missing type for refPre=\n" + refPre
	        + " with class: " + refPre.getClass());
    }

    /**
     * @param refPre
     * @param pv
     * @return an expressions that represents the object to get or set values
     *         from
     */
    public Expression objParam(final ReferencePrefix refPre,
	    final ProgramVariable pv) {
	assert (refPre != null) : "Unexpected null pointer. pv is" + pv;
	if (pv.isStatic()) {
	    // see http://tutorials.jenkov.com/java-reflection/fields.html
	    return new SyntacticalProgramVariable(
		    new ProgramElementName("null"), ((TypeRef) refPre)
		            .getKeYJavaType());
	} else if (refPre instanceof LocationVariable) {
	    final KeYJavaType classOfPv = pv.getContainerType();
	    return new SyntacticalProgramVariable(new ProgramElementName(refPre
		    .toString()), classOfPv);
	} else if (refPre instanceof MethodReference) {
	    return (MethodReference) refPre;
	} else if (refPre instanceof FieldReference) {
	    return callGetter((FieldReference) refPre);
	} else if (refPre instanceof ArrayReference) {
	    return callGetter((ArrayReference) refPre);
	}
	throw new RuntimeException("\nMissing type for refPre=\n" + refPre
	        + " with class: " + refPre.getClass());
    }

    private Expression classParam(final ProgramVariable pv) {
	final KeYJavaType classOfPv = pv.getContainerType();
	return new SyntacticalProgramVariable(new ProgramElementName(classOfPv
	        .getFullName()
	        + ".class"), classOfPv);
    }

    /**
     * @return String representations for all non primitive types
     */
    private HashSet<String> sortsToString() {
	final HashSet<String> result = new HashSet<String>();
	for (final Sort var : usedObjectSorts) {
	    final String sort = var.toString();
	    // We only want Object-Types
	    if (" jbyte jint jlong jfloat jdouble jboolean jchar byte int long float double boolean char "
		    .indexOf(" " + sort + " ") == -1) {
		if (" jbyte[] jint[] jlong[] jfloat[] jdouble[] jboolean[] jchar[] byte[] int[] long[] float[] double[] boolean[] char[] "
		        .indexOf(" " + sort + " ") != -1) {
		    result.add(sort.substring(1));
		} else {
		    result.add(sort);
		}

	    }
	}
	return result;
    }

    private String varName(final IProgramVariable pv) {
	final String name = pv.name().toString();
	final int index = name.lastIndexOf(":") + 1;
	return name.substring(index);
    }

    private String clean(String s) {
	// WARNING: Make sure this fixed string begins with a SPACE and also
	// ends with a SPACE.
	if (" jbyte jint jlong jfloat jdouble jboolean jchar jbyte[] jint[] jlong[] jfloat[] jdouble[] jboolean[] jchar[] "
	        .indexOf(" " + s + " ") != -1) {
	    s = s.substring(1);
	}
	while (s.indexOf(".") != -1) {
	    s = s.substring(0, s.indexOf(".")) + "_"
		    + s.substring(s.indexOf(".") + 1);
	}
	while (s.indexOf("[]") != -1) {
	    s = s.substring(0, s.indexOf("[]")) + ARRAY
		    + s.substring(s.indexOf("[]") + 2);
	}
	return s;
    }

    /**
     * Class the create the ReflectionFile
     * 
     * @author mbender
     * 
     */
    private class ReflectionClassCreator {

	public StringWriter createClass() {
	    // final HashSet<String> sorts = sortsToString(nonGhostVars);
	    final HashSet<String> sorts = sortsToString();
	    final StringWriter result = new StringWriter();
	    result.append(classDecl());
	    result.append(ghostMapDecls(true));
	    result.append(instanceMethod());
	    result.append(instances(sorts));
	    result.append(getterAndSetter(sorts));
	    result.append(footer());
	    assert checkBraces(result.getBuffer()) : "Something wrong";
	    return result;
	}

	/**
	 * @return Beginning of the class
	 */
	private StringBuffer classDecl() {
	    final StringBuffer r = new StringBuffer();
	    r.append("\n\n");
	    r.append("/* Example of an \"ObjectWrapper\" class. \n");
	    r.append(" * @see http://www.j2ee.me/docs/books/tutorial/reflect/member/ctorInstance.html\n");
	    r.append(" * @see http://objenesis.googlecode.com/svn/docs/tutorial.html\n");
	    r.append(" */\n");
	    r.append("public class " + NAME_OF_CLASS + " {\n");
	    return r;
	}
	
	/** Writes a  hashmap and a utility method for associating ghost/model fiels with objects.
	 * @param ghostMapActive becomes are runtime flag that determins if the hashmap should be enabled or not.*/
	private StringBuffer ghostMapDecls(boolean ghostMapActive){
	    final StringBuffer r = new StringBuffer();
	    r.append("\n");
	    
	    r.append("  private static final String NoSuchFieldExceptionText =\n");
	    r.append("  \"This exception occurs when ghost fields or model fields are used in the code or \" +\n");
	    r.append("  \"if mock objects are used that have different fields, than the real objects. \" +\n");
	    r.append("  \"The tester should extend the handling of such fields in this generated utility class RFL.java.\";\n\n");
	    
	    r.append("  public static boolean ghostMapActive = "+ghostMapActive+";\n\n");

	    r.append("  public static java.util.HashMap<Integer,Object> ghostModelFields = new java.util.HashMap<Integer,Object>();\n\n");

	    r.append("  public static int getHash(Class<?> c, Object obj, String attr){\n");
	    r.append("    return c.hashCode() * (obj!=null?obj.hashCode():1) * attr.hashCode();\n");
	    r.append("  }\n\n");
	    return r;
	}

	/**
	 * @return The method that allows to create new instances
	 */
	private StringBuffer instanceMethod() {
	    final StringBuffer r = new StringBuffer();
	    r.append("\n\n");
	    r.append("  /** The Objenesis library can create instances of classes that have no default constructor. */\n");
	    r.append("  private static org.objenesis.Objenesis objenesis = new org.objenesis.ObjenesisStd();\n\n");
	    r.append("  private static Object newInstance(Class c) throws Exception {\n");
	    r.append("    Object res=objenesis.newInstance(c);\n");
	    r.append("    if (res==null)\n");
	    r.append("      throw new Exception(\"Couldn't create instance of class:\"+c);\n");
	    r.append("  return res;\n");
	    r.append("  }\n");
	    return r;
	}

	/**
	 * @param sorts
	 * @return All calls to create objects for the given sorts
	 */
	private StringBuffer instances(final HashSet<String> sorts) {
	    final StringBuffer r = new StringBuffer();
	    r.append("\n  // ---The methods for object creation---\n\n");
	    for (final String sort : sorts) {
		r.append(newRef(sort));
	    }
	    r.append("\n");
	    return r;
	}

	/**
	 * @param sort
	 * @return The call to create an object of given type
	 */
	private StringBuffer newRef(final String sort) {
	    if (sort.indexOf('[') != -1) {
		return newArray(sort);
	    } else {
		return newInstance(sort);
	    }
	}

	/**
	 * @param sort
	 * @return The call to create an object of given type
	 */
	private StringBuffer newInstance(final String sort) {
	    final StringBuffer r = new StringBuffer();
	    r.append("\n");
	    r.append("  public static " + sort + " new" + clean(sort)   + "() throws java.lang.RuntimeException {\n");
	    r.append("    try{\n");
	    r.append("      return (" + sort + ")newInstance(" + sort  + ".class);\n");
	    r.append("    } catch (java.lang.Throwable e) {\n");
	    r.append("       throw new java.lang.RuntimeException(e);\n");
	    r.append("    }\n");
	    r.append("  }\n");
	    return r;
	}

	/**
	 * @param sort
	 * @return The call to create an Array of given type
	 */
	private StringBuffer newArray(final String sort) {
	    final StringBuffer r = new StringBuffer();
	    r.append("\n");
	    r.append("  public static " + sort + " new" + clean(sort)
		    + "(int dim){\n");
	    r.append("    return new " + sort.substring(0, sort.length() - 2)
		    + "[dim];\n");
	    r.append("  }\n");
	    return r;
	}

	private StringBuffer getterAndSetter(final HashSet<String> sorts) {
	    final StringBuffer result = new StringBuffer();
	    result
		    .append("\n  // ---Getter and setter for primitive types---\n");
	    for (int i = 0; i < 7; i++) {
		result.append("\n");
		result.append(declareSetter(PRIMITIVE_TYPES[i], true));
		result.append(declareGetter(PRIMITIVE_TYPES[i],
		        PRIM_TYP_DEF_VAL[i], true));
	    }
	    result.append("\n");
	    result
		    .append("\n  // ---Getter and setter for Reference types---\n");
	    for (final String sort : sorts) {
		result.append("\n");
		result.append(declareSetter(sort, false));
		result.append(declareGetter(sort, "null", false));
	    }
	    return result;
	}

	private StringBuffer declareSetter(final String sort, final boolean prim) {
	    final StringBuffer r = new StringBuffer();
	    final String cmd = "      "+(prim ? 
		      "f.set" + Character.toUpperCase(sort.charAt(0)) + sort.substring(1)+ "(obj, val);\n" 
		    : "f.set(obj, val);\n");
	    r.append("\n");
	    r.append("  public static void _set_" + clean(sort)
		    + "(Class<?> c, Object obj, String attr, " + sort
		    + " val) throws RuntimeException{\n");
	    r.append("    try {\n");
	    r.append("      java.lang.reflect.Field f = c.getDeclaredField(attr);\n");
	    r.append("      f.setAccessible(true);\n");
	    r.append(cmd);
	    r.append("    } catch(NoSuchFieldException e) {\n");
	    r.append("      if(ghostMapActive)\n");
	    r.append("        ghostModelFields.put(getHash(c,obj,attr), val);\n");
	    r.append("      else\n");
	    r.append("        throw new RuntimeException(e.toString() + NoSuchFieldExceptionText);\n");
	    r.append("    } catch(Exception e) {\n");
	    r.append("      throw new RuntimeException(e);\n");
	    r.append("    }\n");
	    r.append("  }\n");
	    return r;
	}
	
	private String primToWrapClass(String sort){
	    if(sort.equals("int"))
		return "Integer";
	    else if(sort.equals("char"))
		return "Character";
	    else
		return Character.toUpperCase(sort.charAt(0)) + sort.substring(1);
	}

	private StringBuffer declareGetter(final String sort, final String def,
	        final boolean prim) {
	    final StringBuffer r = new StringBuffer();
	    final String cmd = "      "+(prim ? 
		    "return f.get" + Character.toUpperCase(sort.charAt(0)) + sort.substring(1)+ "(obj);\n" 
		  : "return (" + sort + ") f.get(obj);\n");
	    r.append("\n");
	    r.append("  public static "
		            + sort
		            + " _get_"
		            + clean(sort)
		            + "(Class<?> c, Object obj, String attr) throws RuntimeException{\n");
	    r.append("    " + sort + " res = " + def + ";\n");
	    r.append("    try {\n");
	    r.append("      java.lang.reflect.Field f = c.getDeclaredField(attr);\n");
	    r.append("      f.setAccessible(true);\n");
	    r.append(cmd);
	    r.append("      } catch(NoSuchFieldException e) {\n");
	    r.append("      return ("+ (prim? primToWrapClass(sort) : sort) +")ghostModelFields.get(getHash(c,obj,attr));\n");
	    r.append("    } catch(Exception e) {\n");
	    r.append("      throw new RuntimeException(e);\n");
	    r.append("    }\n");
	    r.append("  }\n");
	    return r;
	}

	/**
	 * @return the closing bracket and a newline for the end of the class
	 */
	private String footer() {
	    return "}\n";
	}

	private boolean checkBraces(final StringBuffer buf) {
	    int curly = 0;
	    int round = 0;
	    int edged = 0;
	    for (int i = 0; i < buf.length(); i++) {
		switch (buf.charAt(i)) {
		case '{':
		    curly++;
		    break;
		case '}':
		    curly--;
		    break;
		case '(':
		    round++;
		    break;
		case ')':
		    round--;
		    break;
		case '[':
		    edged++;
		    break;
		case ']':
		    edged--;
		    break;
		}
	    }
	    return (curly == 0 && round == 0 && edged == 0);
	}

    }
}
