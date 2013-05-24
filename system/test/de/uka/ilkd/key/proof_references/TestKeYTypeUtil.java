package de.uka.ilkd.key.proof_references;

import java.io.File;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * Tests {@link KeYTypeUtil}.
 * @author Martin Hentschel
 */
public class TestKeYTypeUtil extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests {@link KeYTypeUtil#isInnerType(Services, KeYJavaType)}.
    */
   public void testIsInnerType() throws Exception {
      KeYEnvironment<?> environment = KeYEnvironment.load(new File(keyRepDirectory, "examples/_testcase/proofReferences/InnerAndAnonymousTypeTest"), null, null);
      try {
         Services services = environment.getServices();
         assertNotNull(services);
         // Get KeYJavaTypes to test
         KeYJavaType typeWithoutPackage = KeYTypeUtil.getType(services, "InnerAndAnonymousTypeTest");
         assertNotNull(typeWithoutPackage);
         KeYJavaType typeWithPackage = KeYTypeUtil.getType(services, "model.InnerAndAnonymousTypeTest");
         assertNotNull(typeWithPackage);
         KeYJavaType innerTypeWithoutPackage = KeYTypeUtil.getType(services, "InnerAndAnonymousTypeTest.IGetter");
         assertNotNull(innerTypeWithoutPackage);
         KeYJavaType innerTypeWithPackage = KeYTypeUtil.getType(services, "model.InnerAndAnonymousTypeTest.IGetter");
         assertNotNull(innerTypeWithPackage);
         // Test null
         assertFalse(KeYTypeUtil.isInnerType(services, null));
         assertFalse(KeYTypeUtil.isInnerType(null, typeWithoutPackage));
         assertFalse(KeYTypeUtil.isInnerType(null, null));
         // Test class without package
         assertFalse(KeYTypeUtil.isInnerType(services, typeWithoutPackage));
         // Test class with package
         assertFalse(KeYTypeUtil.isInnerType(services, typeWithPackage));
         // Test inner class without package
         assertTrue(KeYTypeUtil.isInnerType(services, innerTypeWithoutPackage));
         // Test inner class with package
         assertTrue(KeYTypeUtil.isInnerType(services, innerTypeWithPackage));
      }
      finally {
         environment.dispose();
      }
   }
   
   /**
    * Tests {@link KeYTypeUtil#getParentName(Services, KeYJavaType)}.
    */
   public void testGetParentName() throws Exception {
      KeYEnvironment<?> environment = KeYEnvironment.load(new File(keyRepDirectory, "examples/_testcase/proofReferences/InnerAndAnonymousTypeTest"), null, null);
      try {
         Services services = environment.getServices();
         assertNotNull(services);
         // Get KeYJavaTypes to test
         KeYJavaType typeWithoutPackage = KeYTypeUtil.getType(services, "InnerAndAnonymousTypeTest");
         assertNotNull(typeWithoutPackage);
         KeYJavaType typeWithPackage = KeYTypeUtil.getType(services, "model.InnerAndAnonymousTypeTest");
         assertNotNull(typeWithPackage);
         KeYJavaType innerTypeWithoutPackage = KeYTypeUtil.getType(services, "InnerAndAnonymousTypeTest.IGetter");
         assertNotNull(innerTypeWithoutPackage);
         KeYJavaType innerTypeWithPackage = KeYTypeUtil.getType(services, "model.InnerAndAnonymousTypeTest.IGetter");
         assertNotNull(innerTypeWithPackage);
         // Test null
         assertNull(KeYTypeUtil.getParentName(services, null));
         assertNull(KeYTypeUtil.getParentName(null, typeWithoutPackage));
         assertNull(KeYTypeUtil.getParentName(null, null));
         // Test class without package
         assertNull(KeYTypeUtil.getParentName(services, typeWithoutPackage));
         // Test class with package
         assertEquals("model", KeYTypeUtil.getParentName(services, typeWithPackage));
         // Test inner class without package
         assertEquals("InnerAndAnonymousTypeTest", KeYTypeUtil.getParentName(services, innerTypeWithoutPackage));
         // Test inner class with package
         assertEquals("model.InnerAndAnonymousTypeTest", KeYTypeUtil.getParentName(services, innerTypeWithPackage));
      }
      finally {
         environment.dispose();
      }
   }
   
   /**
    * Tests {@link KeYTypeUtil#isType(Services, String)}.
    */
   public void testIsType() throws Exception {
      KeYEnvironment<?> environment = KeYEnvironment.load(new File(keyRepDirectory, "examples/_testcase/proofReferences/InnerAndAnonymousTypeTest"), null, null);
      try {
         Services services = environment.getServices();
         assertNotNull(services);
         // Test null
         assertFalse(KeYTypeUtil.isType(services, null));
         assertFalse(KeYTypeUtil.isType(null, "InnerAndAnonymousTypeTest"));
         assertFalse(KeYTypeUtil.isType(null, null));
         // Test invalid names
         assertFalse(KeYTypeUtil.isType(services, "Invalid")); 
         assertFalse(KeYTypeUtil.isType(services, "model.Invalid")); 
         assertFalse(KeYTypeUtil.isType(services, "invalid.Invalid")); 
         assertFalse(KeYTypeUtil.isType(services, "InnerAndAnonymousTypeTest.Invalid")); 
         assertFalse(KeYTypeUtil.isType(services, "model.InnerAndAnonymousTypeTest.Invalid")); 
         // Test class without package
         assertTrue(KeYTypeUtil.isType(services, "InnerAndAnonymousTypeTest"));
         // Test class with package
         assertTrue(KeYTypeUtil.isType(services, "model.InnerAndAnonymousTypeTest"));
         // Test inner class without package
         assertTrue(KeYTypeUtil.isType(services, "InnerAndAnonymousTypeTest.IGetter"));
         // Test inner class with package
         assertTrue(KeYTypeUtil.isType(services, "model.InnerAndAnonymousTypeTest.IGetter"));
      }
      finally {
         environment.dispose();
      }
   }
   
   /**
    * Tests {@link KeYTypeUtil#getType(de.uka.ilkd.key.java.Services, String)}.
    */
   public void testGetType() throws Exception {
      KeYEnvironment<?> environment = KeYEnvironment.load(new File(keyRepDirectory, "examples/_testcase/proofReferences/InnerAndAnonymousTypeTest"), null, null);
      try {
         Services services = environment.getServices();
         assertNotNull(services);
         // Test null
         assertNull(KeYTypeUtil.getType(services, null));
         assertNull(KeYTypeUtil.getType(null, "InnerAndAnonymousTypeTest"));
         assertNull(KeYTypeUtil.getType(null, null));
         // Test invalid names
         assertNull(KeYTypeUtil.getType(services, "Invalid")); 
         assertNull(KeYTypeUtil.getType(services, "model.Invalid")); 
         assertNull(KeYTypeUtil.getType(services, "invalid.Invalid")); 
         assertNull(KeYTypeUtil.getType(services, "InnerAndAnonymousTypeTest.Invalid")); 
         assertNull(KeYTypeUtil.getType(services, "model.InnerAndAnonymousTypeTest.Invalid")); 
         // Test class without package
         KeYJavaType kjt = KeYTypeUtil.getType(services, "InnerAndAnonymousTypeTest");
         assertEquals("InnerAndAnonymousTypeTest", kjt.getFullName());
         // Test class with package
         kjt = KeYTypeUtil.getType(services, "model.InnerAndAnonymousTypeTest");
         assertEquals("model.InnerAndAnonymousTypeTest", kjt.getFullName());
         // Test inner class without package
         kjt = KeYTypeUtil.getType(services, "InnerAndAnonymousTypeTest.IGetter");
         assertEquals("InnerAndAnonymousTypeTest.IGetter", kjt.getFullName());
         // Test inner class with package
         kjt = KeYTypeUtil.getType(services, "model.InnerAndAnonymousTypeTest.IGetter");
         assertEquals("model.InnerAndAnonymousTypeTest.IGetter", kjt.getFullName());
      }
      finally {
         environment.dispose();
      }
   }
}
