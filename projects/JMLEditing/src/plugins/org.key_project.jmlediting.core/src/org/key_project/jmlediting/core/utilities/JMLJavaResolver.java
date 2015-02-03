package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;

/**
 * Utility Class to resolve TypeBindings.
 *
 * @author Thomas Glaser
 *
 */
public class JMLJavaResolver {
   private final ITypeBinding topType;
   private final ITypeBinding activeType;

   public static boolean debugVisibility = false;

   /**
    *
    * @param activeType
    *           the Type the visibility has to be checked from
    * @return
    */
   public JMLJavaResolver(final ITypeBinding topType,
         final ITypeBinding activeType) {
      this.activeType = activeType;
      this.topType = topType;
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

      for (final IVariableBinding varBind : this
            .getAllVisibleVariableBindings()) {
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
      final int modifier = variable.getModifiers();
      // which modifier is set?
      final boolean isPublic = Modifier.isPublic(modifier);
      final boolean isPrivate = Modifier.isPrivate(modifier);
      final boolean isProtected = Modifier.isProtected(modifier);
      final boolean isPackage = !isPublic && !isPrivate && !isProtected;
      if (debugVisibility) {
         System.out.println("VISIBILITY for " + variable.getName() + " from "
               + variable.getDeclaringClass().getName() + " in "
               + this.activeType.getName() + ":");
         System.out.println();
         System.out.println("declaring: "
               + variable.getDeclaringClass().getName());
         System.out.println("active: " + this.activeType.getName());
         System.out.println("top: " + this.topType.getName());
         System.out.println();
         System.out.println("isPrivate?\t\t" + isPrivate);
         System.out.println("isPublic?\t\t" + isPublic);
         System.out.println("isProtected?\t\t" + isProtected);
         System.out.println("isPackage?\t\t" + isPackage);
      }

      // compute the visibilities
      final boolean isPackageVisible;
      final boolean isProtectedVisible;
      final boolean isPrivateVisible;

      // private
      if (variable.getDeclaringClass().isEqualTo(this.topType)
            || (this.checkNested() && variable.getDeclaringClass().isEqualTo(
                  this.activeType))) {
         // compute the different conditions which define Visibility for
         // different modifiers

         final boolean ifNestedThenInSameClass = !variable.getDeclaringClass()
               .isNested()
               || variable.getDeclaringClass().getDeclaringClass() == this.topType;

         isPrivateVisible = isPrivate && ifNestedThenInSameClass;

         if (debugVisibility) {
            System.out.println();
            System.out.println("ifNestedThenInSameClass? "
                  + ifNestedThenInSameClass);
         }
      }
      else {
         isPrivateVisible = false;
      }

      // package & protected
      if (this.activeType.isEqualTo(this.topType) || this.checkNested()
            || this.checkSameSuperClass(variable.getDeclaringClass())) {
         final boolean isInSamePackage = this.activeType.getPackage()
               .isEqualTo(variable.getDeclaringClass().getPackage());
         final boolean isFromSuperClass = variable.getDeclaringClass()
               .isCastCompatible(this.activeType)
               || (this.checkNested() && variable.getDeclaringClass()
                     .isCastCompatible(this.topType));

         isProtectedVisible = isProtected
               && (isInSamePackage || isFromSuperClass);
         isPackageVisible = isPackage && isInSamePackage;

         if (debugVisibility) {
            System.out.println("isInSamePackage?\t" + isInSamePackage);
            System.out.println("isFromSuperClass?\t" + isFromSuperClass);
         }
      }
      else {
         isProtectedVisible = false;
         isPackageVisible = false;
      }

      if (debugVisibility) {
         System.out.println();
         System.out.println("isPackageVisible?\t" + isPackageVisible);
         System.out.println("isProtectedVisible?\t" + isProtectedVisible);
         System.out.println("isPrivateVisible?\t" + isPrivateVisible);
      }

      final boolean result = isPublic || isPackageVisible || isProtectedVisible
            || isPrivateVisible;

      if (debugVisibility) {
         System.out.println("=> visible?\t\t" + result);
         System.out.println("..............");
      }

      // is the variable visible?
      return result;
   }

   public List<IVariableBinding> getAllParameters(
         final JavaContentAssistInvocationContext context) {
      for (final IMethodBinding method : this.activeType.getDeclaredMethods()) {
         System.out.println("method: " + method.getName());
      }

      return Collections.emptyList();
   }

   public List<IVariableBinding> getAllVisibleVariableBindings() {
      return this.getAllVisibleVariableBindings(this.activeType);
   }

   private List<IVariableBinding> getAllVisibleVariableBindings(
         final ITypeBinding searchType) {
      final List<IVariableBinding> result = new ArrayList<IVariableBinding>();
      ITypeBinding recursiveType = searchType;

      // recursively search for visible variables in SuperClasses
      do {
         for (final IVariableBinding varBind : recursiveType
               .getDeclaredFields()) {
            if (this.isVariableVisible(varBind)) {
               result.add(varBind);
            }
         }
      }
      while ((recursiveType = recursiveType.getSuperclass()) != null);

      if (searchType.isNested()
            && searchType.getDeclaringClass().isEqualTo(this.topType)) {
         if (JMLJavaResolver.debugVisibility) {
            System.out.println("DOING NESTED THINGY... for "
                  + searchType.getName());
         }
         result.addAll(this.getAllVisibleVariableBindings(this.topType));
      }

      return result;
   }

   private boolean checkNested() {
      return this.activeType.isNested()
            && this.activeType.getDeclaringClass().isEqualTo(this.topType);
   }

   private boolean checkSameSuperClass(final ITypeBinding potentialSuperClass) {
      return potentialSuperClass.isCastCompatible(this.activeType)
            && potentialSuperClass.isCastCompatible(this.topType);
   }
}
