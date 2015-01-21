package org.key_project.jmlediting.core.utilities;

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
   private final boolean withProtectedOrInline;

   private JMLJavaResolver(final ITypeBinding activeType,
         final boolean withProtectedOrInline) {
      this.activeType = activeType;
      this.withProtectedOrInline = withProtectedOrInline;
   }

   public static JMLJavaResolver getInstance(final ITypeBinding activeType,
         final boolean withProtectedOrInline) {
      return new JMLJavaResolver(activeType, withProtectedOrInline);
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

      // local variables
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
      // TODO see JavaDoc of getSuperclass() and do the
      // ast.resolveWellKnownType("java.lang.object")... thingy
      else if (active.getSuperclass() != null) {
         this.getTypeForName(active.getSuperclass(), fieldName);
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
      final boolean isDefault = !isPublic && !isPrivate && !isProtected;

      // compute the visibilities
      final boolean isDefaultVisible = isDefault
            && (this.activeType.getPackage().isEqualTo(variable.getType()
                  .getPackage()));

      boolean isProtectedVisible = false;
      boolean isPrivateVisible = false;

      // only compute those visibilities for the first call
      if (this.withProtectedOrInline) {
         isProtectedVisible = isProtected
               && variable.getDeclaringClass()
                     .isCastCompatible(this.activeType);

         isPrivateVisible = isPrivate
               && !variable.getDeclaringClass().isNested();
      }

      // combine the computed visibilities
      return isPublic || isDefaultVisible || isProtectedVisible
            || isPrivateVisible;
   }
}
