/**
 */
package org.key_project.stubby.model.dependencymodel.tests;

import junit.framework.TestCase;

import junit.textui.TestRunner;

import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.stubby.model.dependencymodel.DependencymodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Dependency Model</b></em>'.
 * <!-- end-user-doc -->
 * @generated
 */
public class DependencyModelTest extends TestCase {

   /**
    * The fixture for this Dependency Model test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DependencyModel fixture = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static void main(String[] args) {
      TestRunner.run(DependencyModelTest.class);
   }

   /**
    * Constructs a new Dependency Model test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DependencyModelTest(String name) {
      super(name);
   }

   /**
    * Sets the fixture for this Dependency Model test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void setFixture(DependencyModel fixture) {
      this.fixture = fixture;
   }

   /**
    * Returns the fixture for this Dependency Model test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DependencyModel getFixture() {
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
      setFixture(DependencymodelFactory.eINSTANCE.createDependencyModel());
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

} //DependencyModelTest
