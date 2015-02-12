package org.key_project.key4eclipse.resources.projectinfo;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;

/**
 * Represents a package as known by KeY.
 * @author Martin Hentschel
 */
public class PackageInfo extends AbstractTypeContainer {
   /**
    * The name of the default package.
    */
   public static final String DEFAULT_NAME = "(default package)";

   /**
    * The name.
    */
   private final String name;
   
   /**
    * The {@link IContainer} in eclipse which represents this package.
    */
   private final IContainer container;
   
   /**
    * Constructor.
    * @param projectInfo The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    * @param name The name.
    * @param container The {@link IContainer} in eclipse which represents this package.
    */
   public PackageInfo(ProjectInfo projectInfo, String name, IContainer container) {
      super(projectInfo);
      Assert.isNotNull(name);
      this.name = name;
      this.container = container;
   }

   /**
    * Returns the name.
    * @return the name.
    */
   public String getName() {
      return name;
   }

   /**
    * Returns the {@link IContainer} in eclipse which represents this package.
    * @return The {@link IContainer} in eclipse which represents this package.
    */
   public IContainer getContainer() {
      return container;
   }

   /**
    * Tries to find the {@link IPackageFragment} represented by this package.
    * @return The found {@link IPackageFragment} or {@code null} if not available.
    */
   public IPackageFragment findJDTPackage() {
      if (container != null && container.exists()) {
         IJavaElement javaElement = JavaCore.create(container);
         if (javaElement instanceof IPackageFragmentRoot) {
            IPackageFragmentRoot pr = (IPackageFragmentRoot)javaElement;
            IPackageFragment pf = pr.getPackageFragment(IPackageFragment.DEFAULT_PACKAGE_NAME);
            if (pf.getResource() == javaElement.getResource()) {
               return pf;
            }
            else {
               return null;
            }
         }
         else if (javaElement instanceof IPackageFragment) {
            return (IPackageFragment)javaElement;
         }
      }
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return name;
   }
}
