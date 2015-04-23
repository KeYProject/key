package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Modifier;

/**
 * Utility Class to calculate visible field. The following code snippet is used
 * to examplify the meanings of context type, visibility test and target type.
 *
 * <code>
 * class T {
 *
 *   class Y{}
 * 
 *   void foo() {
 *     Y y;
 *     y.[test here];
 *   }
 * } </code>
 *
 * A visibility test means to find all visibly fields for an object of the
 * target type in a given context type. When performing the test on the object
 * y, the context type is T and the target type is Y.
 *
 * @author Thomas Glaser
 *
 */
public class JMLJavaVisibleFieldsComputer {

   private final ITypeBinding contextType;

   public static boolean debugVisibility = false;

   /**
    * Creates a new instance for the given context type. The context type is the
    * type is which the visibility test is performed.
    *
    * @param contextType
    *           the type, in which the access visibiliy is performed.
    */
   public JMLJavaVisibleFieldsComputer(final ITypeBinding contextType) {
      this.contextType = contextType;
   }

   /**
    * A method to find the Type for a given name.
    *
    * @param targetType
    *           the target type for which the visibility check is performed
    * @param fieldName
    *           the name of the field to check whether it is visible
    *
    * @return the ITypeBinding for the given name or null if the fieldName is
    *         not found
    */
   public ITypeBinding getTypeForName(final ITypeBinding targetType,
         final String fieldName) {
      IVariableBinding foundBinding = null;

      for (final IVariableBinding varBind : this
            .getAllVisibleFields(targetType)) {
         if (fieldName.equals(varBind.getName())) {
            foundBinding = varBind;
            break;
         }
      }
      if (foundBinding != null) {
         return foundBinding.getType();
      }

      return null;
   }

   /**
    * A method to determine whether a variable is visible from the current
    * activeType.
    *
    * @param variable
    *           the variable to check
    * @return true if variable is Visible, else false
    */
   public boolean isVariableVisible(final IVariableBinding variable) {

      final ITypeBinding declaringType = variable.getDeclaringClass();
      final int modifier = variable.getModifiers();
      // which modifier is set?
      final boolean isPublic = Modifier.isPublic(modifier);
      final boolean isPrivate = Modifier.isPrivate(modifier);
      final boolean isProtected = Modifier.isProtected(modifier);
      final boolean isPackage = !isPublic && !isPrivate && !isProtected;

      // Public is always visible
      if (isPublic) {
         return true;
      }

      // Always visible if access is in inner class (or in same class)
      final boolean accessInSameClass = this.memberOfDeclaredClassHierachy(
            declaringType, this.contextType);
      if (accessInSameClass) {
         return true;
      }

      // Access in same package
      final boolean accessInSamePackage = declaringType.getPackage().isEqualTo(
            this.contextType.getPackage());
      final boolean isPackageVisible = (isPackage || isProtected)
            && accessInSamePackage;
      if (isPackageVisible) {
         return true;
      }

      // Protected access in subclasses
      final boolean accessInSubClass = this.contextType
            .isCastCompatible(declaringType);
      final boolean isProtectedVisible = isProtected && accessInSubClass;
      if (isProtectedVisible) {
         return true;
      }

      // Only for completeness ... but is accessInSameClass is true, we have
      // already returned
      final boolean isPrivateVisible = isPrivate && accessInSameClass;

      return isPrivateVisible;
   }

   /**
    * Calculates all visible fields for the given target type in the context
    * type.
    *
    * @param targetType
    *           the type to calculate the visible fields for.
    * @return the list of all visible fields
    */
   public List<IVariableBinding> getAllVisibleFields(
         final ITypeBinding targetType) {

      final List<IVariableBinding> result = new ArrayList<IVariableBinding>();
      ITypeBinding recursiveType = targetType;

      // recursively search for visible variables in SuperClasses
      while (recursiveType != null) {
         for (final IVariableBinding varBind : recursiveType
               .getDeclaredFields()) {
            if (this.isVariableVisible(varBind)) {
               result.add(varBind);
            }
         }
         recursiveType = recursiveType.getSuperclass();
      }

      return result;
   }

   private boolean memberOfDeclaredClassHierachy(final ITypeBinding type,
         final ITypeBinding member) {
      ITypeBinding current = type;
      while (current != null) {
         if (current.isEqualTo(member)) {
            return true;
         }
         current = current.getDeclaringClass();
      }
      return false;
   }
}
