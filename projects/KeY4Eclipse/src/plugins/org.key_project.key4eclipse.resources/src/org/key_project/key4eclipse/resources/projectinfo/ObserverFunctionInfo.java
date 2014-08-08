package org.key_project.key4eclipse.resources.projectinfo;

import org.eclipse.core.runtime.Assert;

/**
 * Represents an observer function as known by KeY.
 * @author Martin Hentschel
 */
public class ObserverFunctionInfo extends AbstractContractContainer {
   /**
    * The {@link TypeInfo} in which this {@link ObserverFunctionInfo} is contained in.
    */
   private final TypeInfo parent;
   
   /**
    * The display name.
    */
   private final String displayName;

   /**
    * Constructor.
    * @param projectInfo The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    * @param parent The {@link TypeInfo} in which this {@link ObserverFunctionInfo} is contained in.
    * @param displayName The display name.
    */
   public ObserverFunctionInfo(ProjectInfo projectInfo, TypeInfo parent, String displayName) {
      super(projectInfo);
      Assert.isNotNull(parent);
      Assert.isNotNull(displayName);
      this.displayName = displayName;
      this.parent = parent;
   }

   /**
    * Returns the {@link TypeInfo} in which this {@link ObserverFunctionInfo} is contained in.
    * @return The {@link TypeInfo} in which this {@link ObserverFunctionInfo} is contained in.
    */
   public TypeInfo getParent() {
      return parent;
   }

   /**
    * Returns the display name.
    * @return The display name.
    */
   public String getDisplayName() {
      return displayName;
   }
}
