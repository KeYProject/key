/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Type</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getMethods <em>Methods</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getFields <em>Fields</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getKind <em>Kind</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#isFinal <em>Final</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#isStatic <em>Static</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getExtends <em>Extends</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getImplements <em>Implements</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getInnerTypes <em>Inner Types</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#isAbstract <em>Abstract</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getPackage <em>Package</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Type#getSimpleName <em>Simple Name</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType()
 * @model
 * @generated
 */
public interface Type extends AbstractType, ITypeVariableContainer {
   /**
    * Returns the value of the '<em><b>Methods</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.Method}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Methods</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Methods</em>' containment reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Methods()
    * @model containment="true"
    * @generated
    */
   EList<Method> getMethods();

   /**
    * Returns the value of the '<em><b>Fields</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.Field}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Fields</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Fields</em>' containment reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Fields()
    * @model containment="true"
    * @generated
    */
   EList<Field> getFields();

   /**
    * Returns the value of the '<em><b>Kind</b></em>' attribute.
    * The literals are from the enumeration {@link org.key_project.stubby.model.dependencymodel.TypeKind}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Kind</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Kind</em>' attribute.
    * @see org.key_project.stubby.model.dependencymodel.TypeKind
    * @see #setKind(TypeKind)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Kind()
    * @model
    * @generated
    */
   TypeKind getKind();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Type#getKind <em>Kind</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Kind</em>' attribute.
    * @see org.key_project.stubby.model.dependencymodel.TypeKind
    * @see #getKind()
    * @generated
    */
   void setKind(TypeKind value);

   /**
    * Returns the value of the '<em><b>Visibility</b></em>' attribute.
    * The literals are from the enumeration {@link org.key_project.stubby.model.dependencymodel.Visibility}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Visibility</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Visibility</em>' attribute.
    * @see org.key_project.stubby.model.dependencymodel.Visibility
    * @see #setVisibility(Visibility)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Visibility()
    * @model
    * @generated
    */
   Visibility getVisibility();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Type#getVisibility <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Visibility</em>' attribute.
    * @see org.key_project.stubby.model.dependencymodel.Visibility
    * @see #getVisibility()
    * @generated
    */
   void setVisibility(Visibility value);

   /**
    * Returns the value of the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Final</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Final</em>' attribute.
    * @see #setFinal(boolean)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Final()
    * @model
    * @generated
    */
   boolean isFinal();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Type#isFinal <em>Final</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Final</em>' attribute.
    * @see #isFinal()
    * @generated
    */
   void setFinal(boolean value);

   /**
    * Returns the value of the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Static</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Static</em>' attribute.
    * @see #setStatic(boolean)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Static()
    * @model
    * @generated
    */
   boolean isStatic();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Type#isStatic <em>Static</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Static</em>' attribute.
    * @see #isStatic()
    * @generated
    */
   void setStatic(boolean value);

   /**
    * Returns the value of the '<em><b>Extends</b></em>' reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.AbstractType}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Extends</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Extends</em>' reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Extends()
    * @model
    * @generated
    */
   EList<AbstractType> getExtends();

   /**
    * Returns the value of the '<em><b>Implements</b></em>' reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.AbstractType}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Implements</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Implements</em>' reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Implements()
    * @model
    * @generated
    */
   EList<AbstractType> getImplements();

   /**
    * Returns the value of the '<em><b>Inner Types</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.Type}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Inner Types</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Inner Types</em>' containment reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_InnerTypes()
    * @model containment="true"
    * @generated
    */
   EList<Type> getInnerTypes();

   /**
    * Returns the value of the '<em><b>Abstract</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Abstract</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Abstract</em>' attribute.
    * @see #setAbstract(boolean)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Abstract()
    * @model
    * @generated
    */
   boolean isAbstract();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Type#isAbstract <em>Abstract</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Abstract</em>' attribute.
    * @see #isAbstract()
    * @generated
    */
   void setAbstract(boolean value);

   /**
    * Returns the value of the '<em><b>Package</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Package</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Package</em>' attribute.
    * @see #setPackage(String)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_Package()
    * @model
    * @generated
    */
   String getPackage();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Type#getPackage <em>Package</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Package</em>' attribute.
    * @see #getPackage()
    * @generated
    */
   void setPackage(String value);

   /**
    * Returns the value of the '<em><b>Simple Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Simple Name</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Simple Name</em>' attribute.
    * @see #setSimpleName(String)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getType_SimpleName()
    * @model
    * @generated
    */
   String getSimpleName();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Type#getSimpleName <em>Simple Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Simple Name</em>' attribute.
    * @see #getSimpleName()
    * @generated
    */
   void setSimpleName(String value);

} // Type
