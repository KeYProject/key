package org.key_project.key4eclipse.common.ui.stubby;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.stubby.core.customization.IGeneratorCustomization;
import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.java.JavaReduxFileCollection;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.util.DirectoryFileCollection;
import de.uka.ilkd.key.util.FileCollection;
import de.uka.ilkd.key.util.FileCollection.Walker;

/**
 * {@link IGeneratorCustomization} for KeY.
 * @author Martin Hentschel
 */
public class KeYGeneratorCustomization implements IGeneratorCustomization {
   /**
    * Is stub folder part of class path?
    */
   private final boolean classPath;
   
   /**
    * Is stub folder the boot class path?
    */
   private final boolean bootClassPath;
   
   /**
    * The full qualified type names of types contained in the boot class path.
    */
   private Set<String> bootTypes;
   
   /**
    * Constructor.
    * @param classPath Is stub folder part of class path?
    * @param bootClassPath Is stub folder the boot class path?
    */
   public KeYGeneratorCustomization(boolean classPath, boolean bootClassPath) {
      this.classPath = classPath;
      this.bootClassPath = bootClassPath;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dependencyModelCreated(IJavaProject javaProject,
                                      String stubFolderPath, 
                                      DependencyModel dependencyModel) throws CoreException {
      try {
         if (classPath) {
            // Open boot class path
            IProject project = javaProject.getProject();
            File file = KeYResourceProperties.getKeYBootClassPathLocation(project);
            FileCollection collection = null;
            if (file == null) {
               collection = new JavaReduxFileCollection(JavaProfile.getDefaultProfile());
            }
            else  {
               collection = new DirectoryFileCollection(file);
            }
            // List types in the boot model
            Walker walker = collection.createWalker(JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
            bootTypes = listTypes(walker);
         }
      }
      catch (IOException e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   /**
    * Lists all full qualified type names contained in the given {@link Walker}.
    * @param walker The {@link Walker} providing java files.
    * @return The qualified type names.
    * @throws IOException Occurred Exception.
    */
   protected Set<String> listTypes(Walker walker) throws IOException {
      final Set<String> result = new HashSet<String>();
      ASTVisitor analyzer = new ASTVisitor() {
         @Override
         public boolean visit(TypeDeclaration node) {
            try {
               StringBuffer sb = new StringBuffer();
               sb.append(node.getName());
               ASTNode parent = node.getParent();
               while (parent != null && !(parent instanceof CompilationUnit)) {
                  sb.insert(0, ".");
                  sb.insert(0, node.getName());
               }
               if (parent instanceof CompilationUnit) {
                  PackageDeclaration pd = ((CompilationUnit) parent).getPackage();
                  if (pd != null) {
                     sb.insert(0, ".");
                     sb.insert(0, pd.getName());
                  }
               }
               result.add(sb.toString());
            }
            catch (Exception e) {
               e.printStackTrace();
            }
            return super.visit(node);
         }
      };
      while (walker.step()) {
         InputStream in = walker.openCurrent();
         try {
            ASTNode ast = JDTUtil.parse(in);
            if (ast != null) {
               ast.accept(analyzer);
            }
         }
         finally {
            in.close();
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stubFolderCreated(IFolder stubFolder) throws CoreException {
      try {
         if (bootClassPath) {
            JavaReduxFileCollection collection = new JavaReduxFileCollection(JavaProfile.getDefaultProfile());
            Walker walker = collection.createWalker(JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
            while (walker.step()) {
               addBootClassPathJavaFile(stubFolder, walker.openCurrent());
            }
         }
      }
      catch (IOException e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   /**
    * Adds the Java file of the given {@link InputStream} to the stub folder.
    * @param stubFolder The stub folder.
    * @param in The {@link InputStream} of the Java file.
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   protected void addBootClassPathJavaFile(IFolder stubFolder, InputStream in) throws IOException, CoreException {
      String content = IOUtil.readFrom(in);
      ASTNode ast = JDTUtil.parse(content);
      if (ast != null) {
         TypeAnalyzer visitor = new TypeAnalyzer();
         ast.accept(visitor);
         TypeDeclaration publicType = visitor.getPublicType();
         if (publicType != null) {
            if (visitor.getPackageDeclaration() != null) {
               String packageDeclaration = visitor.getPackageDeclaration().getName().toString();
               String[] packageFragments = packageDeclaration.split("\\.");
               for (String packageFragment : packageFragments) {
                  stubFolder = stubFolder.getFolder(packageFragment);
                  ResourceUtil.ensureExists(stubFolder);
               }
            }
            IFile file = stubFolder.getFile(publicType.getName() + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
            ResourceUtil.createFile(file, new ByteArrayInputStream(content.getBytes()), null);
         }
      }
   }
   
   /**
    * An {@link ASTVisitor} to list all {@link TypeDeclaration}s.
    * @author Martin Hentschel
    */
   protected static class TypeAnalyzer extends ASTVisitor {
      /**
       * The found {@link TypeDeclaration}
       */
      private final List<TypeDeclaration> types = new LinkedList<TypeDeclaration>();
      
      /**
       * The {@link PackageDeclaration}.
       */
      private PackageDeclaration packageDeclaration;
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean visit(CompilationUnit node) {
         packageDeclaration = node.getPackage();
         return super.visit(node);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean visit(TypeDeclaration node) {
         types.add(node);
         return super.visit(node);
      }

      /**
       * Returns the {@link PackageDeclaration}.
       * @return The {@link PackageDeclaration} or {@code null} if not available.
       */
      public PackageDeclaration getPackageDeclaration() {
         return packageDeclaration;
      }

      /**
       * Returns the public {@link TypeDeclaration}.
       * @return The public {@link TypeDeclaration} or {@code null} if not available.
       */
      public TypeDeclaration getPublicType() {
         if (types.size() == 1) {
            return types.get(0);
         }
         else {
            return CollectionUtil.search(types, new IFilter<TypeDeclaration>() {
               @Override
               public boolean select(TypeDeclaration element) {
                  return Modifier.isPublic(element.getModifiers());
               }
            });
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getIgnoreReason(IJavaProject javaProject, 
                                 String stubFolderPath, 
                                 AbstractType abstractType) throws CoreException {
      if (bootTypes != null &&
          bootTypes.contains(abstractType.getName())) {
         return "Type is part of KeY's boot class path.";
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stubFilesGenerated(IJavaProject javaProject, String stubFolderPath) throws CoreException {
      IProject project = javaProject.getProject();
      final String fullPath = KeYStubGenerationCustomization.computeFullPath(project, stubFolderPath);
      // Ensure that class path is correct according to classPath.
      List<KeYClassPathEntry> entries = KeYResourceProperties.getClassPathEntries(project);
      KeYClassPathEntry entry = KeYResourceProperties.searchClassPathEntry(entries, KeYClassPathEntryKind.WORKSPACE, fullPath);
      if (classPath) {
         if (entry == null) {
            entry = new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, fullPath);
            entries.add(entry);
            KeYResourceProperties.setClassPathEntries(project, entries);
         }
      }
      else {
         if (entry != null) {
            entries.remove(entry);
            KeYResourceProperties.setClassPathEntries(project, entries);
         }
      }
      // Ensure that boot class path is correct according to #bootClassPath.
      boolean isBootClassPath = KeYStubGenerationCustomization.isBootClassPath(project, stubFolderPath);
      if (bootClassPath) {
         if (!isBootClassPath) {
            KeYResourceProperties.setBootClassPath(project, UseBootClassPathKind.WORKSPACE, fullPath);
         }
      }
      else {
         if (isBootClassPath) {
            KeYResourceProperties.setBootClassPath(project, UseBootClassPathKind.KEY_DEFAULT, null);
         }
      }
   }
}
