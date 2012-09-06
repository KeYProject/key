/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package org.key_project.sed.ui.visualization.model.od;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Object</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODObject#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODObject#getType <em>Type</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODObject#getValues <em>Values</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODObject#getAssociations <em>Associations</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODObject()
 * @model
 * @generated
 */
public interface ODObject extends EObject {
   /**
    * Returns the value of the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Name</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Name</em>' attribute.
    * @see #setName(String)
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODObject_Name()
    * @model
    * @generated
    */
   String getName();

   /**
    * Sets the value of the '{@link org.key_project.sed.ui.visualization.model.od.ODObject#getName <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Name</em>' attribute.
    * @see #getName()
    * @generated
    */
   void setName(String value);

   /**
    * Returns the value of the '<em><b>Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Type</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Type</em>' attribute.
    * @see #setType(String)
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODObject_Type()
    * @model
    * @generated
    */
   String getType();

   /**
    * Sets the value of the '{@link org.key_project.sed.ui.visualization.model.od.ODObject#getType <em>Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Type</em>' attribute.
    * @see #getType()
    * @generated
    */
   void setType(String value);

   /**
    * Returns the value of the '<em><b>Values</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.sed.ui.visualization.model.od.ODValue}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Values</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Values</em>' containment reference list.
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODObject_Values()
    * @model containment="true"
    * @generated
    */
   EList<ODValue> getValues();

   /**
    * Returns the value of the '<em><b>Associations</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.sed.ui.visualization.model.od.ODAssociation}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Associations</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Associations</em>' containment reference list.
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODObject_Associations()
    * @model containment="true"
    * @generated
    */
   EList<ODAssociation> getAssociations();

} // ODObject
