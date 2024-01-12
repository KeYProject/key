package test.recoder;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import recoder.DefaultServiceConfiguration;
import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.io.PropertyNames;
import recoder.service.DefaultProgramModelInfo;
import recoder.service.NameInfo;
import recoder.service.ProgramModelInfo;


/**
 * Test the patched methods in {@link DefaultProgramModelInfo}.
 * 
 * There is a new getMethods-method with an argument of type
 * ClassType.
 * 
 * @see DefaultProgramModelInfo#getMethods(ClassType, String, List, List, ClassType)
 * 
 * @author mattias ulbrich
 */
public class GetMethodsTest extends TestCase {

	DefaultProgramModelInfo underTest;
	ServiceConfiguration sc = new DefaultServiceConfiguration();
	NameInfo ni = sc.getNameInfo();
	ClassType classA;
	ClassType classB;
	
	protected void setUp() throws Exception {
		super.setUp();
		if (!sc.getProjectSettings().ensureSystemClassesAreInPath()) {
			fail("Problem with system setup: Cannot locate system classes");	        	
	    }
		sc.getProjectSettings().setProperty(PropertyNames.JAVA_5, "true");
		classA = ni.getClassType("test.A");
		classB = ni.getClassType("test.B");		
	}

	/**
	 * test the method
	 *   
	 *    List<Method> getMethods(ClassType ct, String name, List<Type> signature)
	 *    
	 *  So a call for "method" has to return the private method that has
	 *  an int argument.	
	 *
	 */
	public final void testGetMethods1() {
		ProgramModelInfo pmi = classA.getProgramModelInfo();
		List<Type> signature = new ArrayList<Type>();		
		signature.add(ni.getIntType());
		List<Method> methods = pmi.getMethods(classA, "method", signature);
		assertEquals(1, methods.size());		
		List<Type> signatur = methods.get(0).getSignature(); 
		assertEquals(1, signatur.size());
		assertEquals(ni.getIntType(), signatur.get(0));
	}

	
	/**
	 * test the method 
	 * 
	 *   List<Method> getMethods(ClassType ct, String name, List<Type> signature, 
	 *         List<? extends TypeArgument> typeArgs, ClassType context);
	 *         
	 * where context != ct.
	 * So a call for "method" has to return the public method that 
	 * has an Integer argument.  
	 *
	 */
	public final void testGetMethods2() {
		ProgramModelInfo pmi = classA.getProgramModelInfo();
		ClassType integerClass = ni.getClassType("java.lang.Integer");
		List<Type> signature = new ArrayList<Type>();		
		signature.add(ni.getIntType());
		List<Method> methods = pmi.getMethods(classA, "method", signature, null, classB);
		assertEquals(1, methods.size());		
		List<Type> signatur = methods.get(0).getSignature(); 
		assertEquals(1, signatur.size());
		assertEquals(integerClass, signatur.get(0));
	}

}
