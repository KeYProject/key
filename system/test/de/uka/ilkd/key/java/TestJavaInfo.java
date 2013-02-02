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


package de.uka.ilkd.key.java;

import java.io.File;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;


/**
 * This class tests several methods of the JavaInfo class
 */
public class TestJavaInfo extends TestCase {       
    
    public static final String testfile = System.getProperty("key.home")
    + File.separator + "examples"
    + File.separator + "_testcase" + File.separator
    + "javainfo" + File.separator + "testJavaInfo.key";

    private static Services services;
    private static JavaInfo javaInfo;
        
    private static int down = 0;
    private static int testcases = 0;
    
    
    public TestJavaInfo() {
        testcases++;
    }
    
    public void setUp() {
        if (down != 0) return;
        HelperClassForTests helper =  new HelperClassForTests();
        final ProofAggregate agg = helper.parse(new File(testfile));
        services = agg.getFirstProof().getServices();
        javaInfo = services.getJavaInfo();
    }
    
    public void tearDown() {
        down ++;
        if (testcases>down) return;        
        services = null;
        javaInfo = null;
    }
    
    public void testRetrieveArrayTypeByJLSName() {
        assertTrue("Did not find [I", javaInfo.getKeYJavaType("[I") != null);

        assertTrue("Did not find [java.lang.Object", 
                javaInfo.getKeYJavaType("[Ljava.lang.Object") != null);
    }
    
    public void testRetrieveArrayTypeByAlternativeName() {
        assertTrue("Did not find int[]", javaInfo.getKeYJavaType("int[]") != null);

        assertTrue("Did not find java.lang.Object[]", 
                javaInfo.getKeYJavaType("java.lang.Object[]") != null);
    }
    
    public void testGetAllSubtypes() {
        assertTrue("No subtypes of java.lang.Object?", javaInfo.getAllSubtypes(services.getJavaInfo().getJavaLangObject()) != null);
        // attention this test is not for fun, there are some methods deoending on
        // this property
        assertTrue("The method getAllSubtypes must not contain the type itself", !javaInfo.getAllSubtypes(services.getJavaInfo().getJavaLangObject()).
                 contains(javaInfo.getJavaLangObject()));        
    }
    
    public void testGetAllSupertypes() {
        KeYJavaType rte = javaInfo.getKeYJavaType("java.lang.RuntimeException");
        assertTrue("Did not find class java.lang.RuntimeException", rte != null);
        final ImmutableList<KeYJavaType> allSupertypes = javaInfo.getAllSupertypes(rte);
        
        assertTrue("No supertypes of java.lang.RuntimeException?", 
                allSupertypes != null);
       
        assertTrue("The method getAllSupertypes must contain the type itself", 
                allSupertypes.contains(rte));        
    }
    
    public void testFindArrayLength() {
        KeYJavaType intarray = javaInfo.getKeYJavaType("int[]");
        assertTrue("Could not find length attribute for arrays: ", 
                javaInfo.getAttribute("length", intarray) != null);
        
    }
    
    private static final String[] implictFieldsClassOnly = new String[]{
        ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS, ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS,
        ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, ImplicitFieldAdder.IMPLICIT_CLASS_PREPARED
    };
    
    private static final String[] generalImplicitFields = new String[]{
      ImplicitFieldAdder.IMPLICIT_CREATED,
      ImplicitFieldAdder.IMPLICIT_INITIALIZED
    };
    
    
    public void testFindImplicitAttributesForClassTypesOnly() {
        KeYJavaType obj = javaInfo.getKeYJavaType("java.lang.Object");
        for (String generalImplicitField : generalImplicitFields) {
            assertTrue("Could not find " + generalImplicitField +
                    "attribute for arrays.",
                    javaInfo.lookupVisibleAttribute(generalImplicitField,
                            obj) != null);
        }
        for (String anImplictFieldsClassOnly : implictFieldsClassOnly) {
            assertTrue("Could not find " + anImplictFieldsClassOnly +
                    "attribute for arrays.",
                    javaInfo.lookupVisibleAttribute(anImplictFieldsClassOnly,
                            obj) != null);
        }    
    }
    
    /**
     * Important getAttribute methods of javaInfo must return only local declared 
     * attributes
     *
     */
    public void testFindAttributesLocallyDeclaredOnly() {
        KeYJavaType obj = javaInfo.getKeYJavaType("java.lang.Object");
        
        KeYJavaType rte = javaInfo.getKeYJavaType("java.lang.RuntimeException");
        
        
        assertTrue("Did not find locally declared attribute " + ImplicitFieldAdder.IMPLICIT_CREATED,
                javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, obj)!= null);
        
        assertTrue("Attribute " + ImplicitFieldAdder.IMPLICIT_CREATED + 
                " is locally declared in class java.lang.Object and should not be " +
                "returned by this method for type java.lang.RuntimeException",
                javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, rte) == null);
        
    }
    
    /**
     * tests if the common subtypes of two sorts are correctly determined
     */
    public void testGetCommonSubtypes() {       
        
        final KeYJavaType ae = javaInfo.getKeYJavaType("java.lang.ArithmeticException");
        final KeYJavaType npe = javaInfo.getKeYJavaType("java.lang.NullPointerException");
        
        assertTrue(javaInfo.getCommonSubtypes(ae, npe).size() == 0);

        final KeYJavaType obj = javaInfo.getKeYJavaType("java.lang.Object");        
        final KeYJavaType rte = javaInfo.getKeYJavaType("java.lang.RuntimeException");
        
        long start = System.currentTimeMillis();

        final ImmutableList<KeYJavaType> commons = javaInfo.getCommonSubtypes(obj, rte);        
        assertTrue(commons.equals(javaInfo.getAllSubtypes(rte).prepend(rte)));             

        
        long end = System.currentTimeMillis();
        final long duration = end - start;
        
        // test caching
        long durationCache = 0;
        for (int i = 0; i<1000; i++) {          
            start = System.currentTimeMillis();
            final ImmutableList<KeYJavaType> commonsCache = 
                javaInfo.getCommonSubtypes(obj, rte);
            end = System.currentTimeMillis();            
            assertTrue("Cache inconsistence", commonsCache.equals(commons));
            durationCache += end - start;            
        }        
        assertTrue("Performance problem with caching common subsorts", 
                durationCache/1000 < duration || duration == 0 && durationCache/1000 == 0);
        
        
    }
    
    /**
     * test getPrimtiveKeYJavaType
     */
    public void testGetPrimitiveKJT() {
        final String[] primitiveTypeNames = new String[]{
               "long", "int", "short", "byte", "char", "boolean"
        };

        for (String primitiveTypeName : primitiveTypeNames) {
            assertNotNull("Type" + primitiveTypeName + " not found",
                    javaInfo.getPrimitiveKeYJavaType(primitiveTypeName));
        }
        
        assertNull("Ooops, non primitive type found",
                javaInfo.getPrimitiveKeYJavaType("java.lang.Object"));
        assertNull("Ooops, non existing type found",
                javaInfo.getPrimitiveKeYJavaType("myOwnType"));        
    }   
    
}
