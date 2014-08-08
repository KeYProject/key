package org.key_project.key4eclipse.resources.projectinfo;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.util.jdt.JDTUtil;

/**
 * Represents a method as known by KeY.
 * @author Martin Hentschel
 */
public class MethodInfo extends AbstractContractContainer implements IStatusInfo {
   /**
    * The parent {@link TypeInfo} in which this {@link MethodInfo} is contained in.
    */
   private final TypeInfo parent;
   
   /**
    * The display name.
    */
   private final String displayName;
   
   /**
    * The name.
    */
   private final String name;
   
   /**
    * The full qualified parameter type names.
    */
   private final String[] parameterTypes;
   
   /**
    * Constructor.
    * @param projectInfo The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    * @param parent The parent {@link TypeInfo} in which this {@link MethodInfo} is contained in.
    * @param displayName The display name.
    * @param name The name.
    * @param parameterTypes The full qualified parameter type names.
    */
   public MethodInfo(ProjectInfo projectInfo, TypeInfo parent, String displayName, String name, String[] parameterTypes) {
      super(projectInfo);
      Assert.isNotNull(parent);
      Assert.isNotNull(displayName);
      Assert.isNotNull(name);
      Assert.isNotNull(parameterTypes);
      this.parent = parent;
      this.displayName = displayName;
      this.name = name;
      this.parameterTypes = parameterTypes;
   }

   /**
    * Returns the parent {@link TypeInfo} in which this {@link MethodInfo} is contained in.
    * @return The parent {@link TypeInfo} in which this {@link MethodInfo} is contained in.
    */
   public TypeInfo getParent() {
      return parent;
   }

   /**
    * Returns the name.
    * @return The name.
    */
   public String getName() {
      return name;
   }

   /**
    * Returns the display name.
    * @return The display name.
    */
   public String getDisplayName() {
      return displayName;
   }
   
   /**
    * Returns the full qualified parameter type names.
    * @return The full qualified parameter type names.
    */
   public String[] getParameterTypes() {
      return parameterTypes;
   }

   /**
    * Tries to find the {@link IMethod} represented by this method.
    * @return The found {@link IMethod} or {@code null} if not available.
    */
   public IMethod findJDTMethod() throws JavaModelException {
      IType jdtType = parent.findJDTType();
      if (jdtType != null && jdtType.exists()) {
         return JDTUtil.findJDTMethod(jdtType, name, parameterTypes);
      }
      else {
         return null;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isUnspecified() {
      return countContracts() == 0;
   }
}
