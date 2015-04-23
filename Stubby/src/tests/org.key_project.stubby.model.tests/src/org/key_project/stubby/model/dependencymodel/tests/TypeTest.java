/**
 */
package org.key_project.stubby.model.dependencymodel.tests;

import junit.framework.TestCase;
import junit.textui.TestRunner;

import org.key_project.stubby.model.dependencymodel.DependencymodelFactory;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeUsage;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Type</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#containsField(java.lang.String) <em>Contains Field</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#containsMethod(java.lang.String, java.lang.String[]) <em>Contains Method</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public class TypeTest extends TestCase {

   /**
    * The fixture for this Type test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected Type fixture = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static void main(String[] args) {
      TestRunner.run(TypeTest.class);
   }

   /**
    * Constructs a new Type test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public TypeTest(String name) {
      super(name);
   }

   /**
    * Sets the fixture for this Type test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void setFixture(Type fixture) {
      this.fixture = fixture;
   }

   /**
    * Returns the fixture for this Type test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected Type getFixture() {
      return fixture;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see junit.framework.TestCase#setUp()
    * @generated
    */
   @Override
   protected void setUp() throws Exception {
      setFixture(DependencymodelFactory.eINSTANCE.createType());
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see junit.framework.TestCase#tearDown()
    * @generated
    */
   @Override
   protected void tearDown() throws Exception {
      setFixture(null);
   }

   /**
    * Tests the '{@link org.key_project.stubby.model.dependencymodel.Type#containsField(java.lang.String) <em>Contains Field</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.Type#containsField(java.lang.String)
    * @generated NOT
    */
   public void testContainsField__String() {
      // Create model
      Field notNamed = DependencymodelFactory.eINSTANCE.createField();
      Field first = DependencymodelFactory.eINSTANCE.createField();
      first.setName("first");
      Field second = DependencymodelFactory.eINSTANCE.createField();
      second.setName("second");
      Field third = DependencymodelFactory.eINSTANCE.createField();
      third.setName("third");
      Type type = DependencymodelFactory.eINSTANCE.createType();
      type.getFields().add(notNamed);
      type.getFields().add(first);
      type.getFields().add(second);
      type.getFields().add(third);
      // Perform test
      assertTrue(type.containsField(notNamed.getName()));
      assertTrue(type.containsField(first.getName()));
      assertTrue(type.containsField(second.getName()));
      assertTrue(type.containsField(third.getName()));
      assertFalse(type.containsField("notContained"));
   }

   /**
    * Tests the '{@link org.key_project.stubby.model.dependencymodel.Type#containsMethod(java.lang.String, java.lang.String[]) <em>Contains Method</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.Type#containsMethod(java.lang.String, java.lang.String[])
    * @generated NOT
    */
   public void testContainsMethod__String_String() {
      // Create model
      TypeUsage intUsage = DependencymodelFactory.eINSTANCE.createTypeUsage();
      intUsage.setType("int");
      TypeUsage intAgainUsage = DependencymodelFactory.eINSTANCE.createTypeUsage();
      intAgainUsage.setType("int");
      TypeUsage booleanUsage = DependencymodelFactory.eINSTANCE.createTypeUsage();
      booleanUsage.setType("boolean");
      TypeUsage charUsage = DependencymodelFactory.eINSTANCE.createTypeUsage();
      charUsage.setType("char");
      Method notNamed = DependencymodelFactory.eINSTANCE.createMethod();
      Method first = DependencymodelFactory.eINSTANCE.createMethod();
      first.setName("first");
      Method second = DependencymodelFactory.eINSTANCE.createMethod();
      second.setName("second");
      Method third = DependencymodelFactory.eINSTANCE.createMethod();
      third.setName("third");
      Method thirdInt = DependencymodelFactory.eINSTANCE.createMethod();
      thirdInt.setName("third");
      thirdInt.getParameterTypes().add(intUsage);
      Method thirdIntBoolean = DependencymodelFactory.eINSTANCE.createMethod();
      thirdIntBoolean.setName("third");
      thirdIntBoolean.getParameterTypes().add(intAgainUsage);
      thirdIntBoolean.getParameterTypes().add(booleanUsage);
      Method thirdChar = DependencymodelFactory.eINSTANCE.createMethod();
      thirdChar.setName("third");
      thirdChar.getParameterTypes().add(charUsage);
      Type type = DependencymodelFactory.eINSTANCE.createType();
      type.getMethods().add(notNamed);
      type.getMethods().add(first);
      type.getMethods().add(second);
      type.getMethods().add(third);
      type.getMethods().add(thirdInt);
      type.getMethods().add(thirdIntBoolean);
      type.getMethods().add(thirdChar);
      // Perform test
      assertTrue(type.containsMethod(notNamed.getName(), new String[] {}));
      assertTrue(type.containsMethod(first.getName(), new String[] {}));
      assertTrue(type.containsMethod(second.getName(), new String[] {}));
      assertTrue(type.containsMethod(third.getName(), new String[] {}));
      assertTrue(type.containsMethod(third.getName(), new String[] {"int"}));
      assertTrue(type.containsMethod(third.getName(), new String[] {"int", "boolean"}));
      assertTrue(type.containsMethod(third.getName(), new String[] {"char"}));
      assertFalse(type.containsMethod(third.getName(), new String[] {"int", "double"}));
      assertFalse(type.containsMethod(third.getName(), new String[] {"double"}));
      assertFalse(type.containsMethod("notContained", new String[] {}));
   }

} //TypeTest
