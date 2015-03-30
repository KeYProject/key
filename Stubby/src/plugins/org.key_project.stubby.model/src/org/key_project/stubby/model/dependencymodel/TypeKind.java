/**
 */
package org.key_project.stubby.model.dependencymodel;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.emf.common.util.Enumerator;

/**
 * <!-- begin-user-doc -->
 * A representation of the literals of the enumeration '<em><b>Type Kind</b></em>',
 * and utility methods for working with them.
 * <!-- end-user-doc -->
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getTypeKind()
 * @model
 * @generated
 */
public enum TypeKind implements Enumerator {
   /**
    * The '<em><b>CLASS</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #CLASS_VALUE
    * @generated
    * @ordered
    */
   CLASS(0, "CLASS", "CLASS"),

   /**
    * The '<em><b>INTERFACE</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #INTERFACE_VALUE
    * @generated
    * @ordered
    */
   INTERFACE(1, "INTERFACE", "INTERFACE"),

   /**
    * The '<em><b>ENUM</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #ENUM_VALUE
    * @generated
    * @ordered
    */
   ENUM(2, "ENUM", "ENUM"),

   /**
    * The '<em><b>ANNOTATION</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #ANNOTATION_VALUE
    * @generated
    * @ordered
    */
   ANNOTATION(3, "ANNOTATION", "ANNOTATION");

   /**
    * The '<em><b>CLASS</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>CLASS</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #CLASS
    * @model
    * @generated
    * @ordered
    */
   public static final int CLASS_VALUE = 0;

   /**
    * The '<em><b>INTERFACE</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>INTERFACE</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #INTERFACE
    * @model
    * @generated
    * @ordered
    */
   public static final int INTERFACE_VALUE = 1;

   /**
    * The '<em><b>ENUM</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>ENUM</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #ENUM
    * @model
    * @generated
    * @ordered
    */
   public static final int ENUM_VALUE = 2;

   /**
    * The '<em><b>ANNOTATION</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>ANNOTATION</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #ANNOTATION
    * @model
    * @generated
    * @ordered
    */
   public static final int ANNOTATION_VALUE = 3;

   /**
    * An array of all the '<em><b>Type Kind</b></em>' enumerators.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private static final TypeKind[] VALUES_ARRAY =
      new TypeKind[] {
         CLASS,
         INTERFACE,
         ENUM,
         ANNOTATION,
      };

   /**
    * A public read-only list of all the '<em><b>Type Kind</b></em>' enumerators.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static final List<TypeKind> VALUES = Collections.unmodifiableList(Arrays.asList(VALUES_ARRAY));

   /**
    * Returns the '<em><b>Type Kind</b></em>' literal with the specified literal value.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static TypeKind get(String literal) {
      for (int i = 0; i < VALUES_ARRAY.length; ++i) {
         TypeKind result = VALUES_ARRAY[i];
         if (result.toString().equals(literal)) {
            return result;
         }
      }
      return null;
   }

   /**
    * Returns the '<em><b>Type Kind</b></em>' literal with the specified name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static TypeKind getByName(String name) {
      for (int i = 0; i < VALUES_ARRAY.length; ++i) {
         TypeKind result = VALUES_ARRAY[i];
         if (result.getName().equals(name)) {
            return result;
         }
      }
      return null;
   }

   /**
    * Returns the '<em><b>Type Kind</b></em>' literal with the specified integer value.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static TypeKind get(int value) {
      switch (value) {
         case CLASS_VALUE: return CLASS;
         case INTERFACE_VALUE: return INTERFACE;
         case ENUM_VALUE: return ENUM;
         case ANNOTATION_VALUE: return ANNOTATION;
      }
      return null;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private final int value;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private final String name;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private final String literal;

   /**
    * Only this class can construct instances.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private TypeKind(int value, String name, String literal) {
      this.value = value;
      this.name = name;
      this.literal = literal;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public int getValue() {
     return value;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getName() {
     return name;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getLiteral() {
     return literal;
   }

   /**
    * Returns the literal value of the enumerator, which is its string representation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public String toString() {
      return literal;
   }
   
   /**
    * @generated NOT
    */
   public String toJavaKindKeyword() {
      switch (this) {
         case ANNOTATION : return "@interface";
         case CLASS : return "class";
         case ENUM : return "enum";
         case INTERFACE : return "interface";
         default : throw new IllegalStateException();
      }
   }
   
} //TypeKind
