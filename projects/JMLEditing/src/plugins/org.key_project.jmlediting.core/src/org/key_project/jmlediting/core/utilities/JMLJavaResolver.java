package org.key_project.jmlediting.core.utilities;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Modifier;

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
      IVariableBinding foundBinding = null;
      for (final IVariableBinding varBind : this.activeType.getDeclaredFields()) {
         if (this.isVariableVisible(varBind)
               && (fieldName.equals(varBind.getName()))) {
            foundBinding = varBind;
            break;
         }
      }
      if (foundBinding == null) {
         System.out.println("foundBinding == null");
         return null;
      }
      return foundBinding.getType();
   }

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
