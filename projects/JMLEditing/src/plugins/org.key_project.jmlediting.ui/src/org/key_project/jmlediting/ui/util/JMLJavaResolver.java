package org.key_project.jmlediting.ui.util;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Modifier;

public class JMLJavaResolver {
   private final ITypeBinding activeType;

   private JMLJavaResolver(final ITypeBinding activeType) {
      this.activeType = activeType;
   }

   public static JMLJavaResolver getInstance(final ITypeBinding activeType) {
      return new JMLJavaResolver(activeType);
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

      final boolean isPublic = Modifier.isPublic(modifier);
      final boolean isPrivate = Modifier.isPrivate(modifier);
      final boolean isProtected = Modifier.isProtected(modifier);
      final boolean isDefault = !isPublic && !isPrivate && !isProtected;

      final boolean isDefaultVisible = isDefault
            && (this.activeType.getPackage().isEqualTo(variable.getType()
                  .getPackage()));

      System.out.println("public?" + isPublic);
      System.out.println("protected?" + isProtected);
      System.out.println("private?" + isPrivate);
      System.out.println("default?" + isDefault);
      System.out.println("defaultVisible?" + isDefaultVisible);

      final boolean visible = isPublic || isDefaultVisible;
      System.out.println("==> " + visible);
      return visible;
   }
}
