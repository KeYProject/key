package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Modifier;

/**
 *
 * @author Thomas Glaser Utility Class to resolve TypeBindings.
 *
 */
public class JMLJavaResolver {
   private final ITypeBinding activeType;

   /**
    *
    * @param activeType
    *           the Type the visibility has to be checked from
    * @return
    */
   public JMLJavaResolver(final ITypeBinding activeType) {
      this.activeType = activeType;
   }

   public ITypeBinding getTypeForName(final String fieldName) {
      return this.getTypeForName(this.activeType, fieldName);
   }

   /**
    * A method to find the Type for a given name.
    *
    * @param active
    * @param fieldName
    * @return the ITypeBinding for the given name or null if the fieldName is
    *         not found
    */
   private ITypeBinding getTypeForName(final ITypeBinding active,
         final String fieldName) {
      IVariableBinding foundBinding = null;

      for (final IVariableBinding varBind : active.getDeclaredFields()) {
         if (this.isVariableVisible(varBind)
               && (fieldName.equals(varBind.getName()))) {
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
      final int modifier = variable.getModifiers();
      // which modifier is set?
      final boolean isPublic = Modifier.isPublic(modifier);
      final boolean isPrivate = Modifier.isPrivate(modifier);
      final boolean isProtected = Modifier.isProtected(modifier);
      final boolean isPackage = !isPublic && !isPrivate && !isProtected;

      final boolean visibilityDebug = false;

      if (visibilityDebug) {
         System.out.println("VISIBILITY for " + variable.getName() + " in "
               + this.activeType.getName() + ":");
         System.out.println("isPrivate?\t\t" + isPrivate);
         System.out.println("isPublic?\t\t" + isPublic);
         System.out.println("isProtected?\t\t" + isProtected);
         System.out.println("isPackage?\t\t" + isPackage);
      }

      // compute the visibilities
      final boolean isPackageVisible;
      final boolean isProtectedVisible;
      final boolean isPrivateVisible;
      // only compute those visibilities for the first call
      if (variable.getDeclaringClass().isEqualTo(this.activeType)) {
         // compute the different conditions which define Visibility for
         // different modifiers
         final boolean isInSamePackage = this.activeType.getPackage()
               .isEqualTo(variable.getType().getPackage());
         final boolean isFromSuperClass = variable.getDeclaringClass()
               .isCastCompatible(this.activeType);
         final boolean ifNestedThenInSameClass = !variable.getDeclaringClass()
               .isNested()
               || variable.getDeclaringClass().getDeclaringClass() == this.activeType;

         // combine the visibilities
         isProtectedVisible = isProtected
               && (isInSamePackage || isFromSuperClass);

         isPrivateVisible = isPrivate && ifNestedThenInSameClass;

         isPackageVisible = isPackage && isInSamePackage;

         if (visibilityDebug) {
            System.out.println();
            System.out.println("isInSamePackage?\t" + isInSamePackage);
            System.out.println("isFromSuperClass?`\t" + isFromSuperClass);
            System.out.println("ifNestedThenInSameClass? "
                  + ifNestedThenInSameClass);
         }
      }
      else {
         isProtectedVisible = false;
         isPrivateVisible = false;
         isPackageVisible = false;
      }
      if (visibilityDebug) {
         System.out.println();
         System.out.println("isPackageVisible?\t" + isPackageVisible);
         System.out.println("isProtectedVisible?\t" + isProtectedVisible);
         System.out.println("isPrivateVisible?\t" + isPrivateVisible);
      }

      final boolean result = isPublic || isPackageVisible || isProtectedVisible
            || isPrivateVisible;

      if (visibilityDebug) {
         System.out.println("=> visible?\t\t" + result);
         System.out.println("..............");
      }

      // is the variable visible?
      return result;
   }

   public List<IVariableBinding> getAllVisibleVariableBindings() {
      final List<IVariableBinding> result = new ArrayList<IVariableBinding>();

      result.addAll(Arrays.asList(this.activeType.getDeclaredFields()));

      // recursively search for visible variables in SuperClasses
      ITypeBinding recursiveType = this.activeType;
      while ((recursiveType = recursiveType.getSuperclass()) != null) {
         for (final IVariableBinding varBind : recursiveType
               .getDeclaredFields()) {
            if (this.isVariableVisible(varBind)) {
               result.add(varBind);
            }
         }
      }

      return result;
   }
}
