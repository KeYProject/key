package org.key_project.key4eclipse.common.ui.stubby;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry.KeYPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.stubby.core.customization.IGeneratorCustomization;
import org.key_project.stubby.core.jdt.DependencyAnalyzer;
import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.ui.util.KeYExampleUtil;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaReduxFileCollection;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.util.DirectoryFileCollection;
import de.uka.ilkd.key.util.FileCollection;
import de.uka.ilkd.key.util.FileCollection.Walker;
import de.uka.ilkd.key.util.KeYTypeUtil;

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
   public List<? extends IJavaElement> defineSources(IJavaProject javaProject) throws CoreException {
      if (classPath || bootClassPath) {
         IResource sourceResource = KeYResourceProperties.getSourceClassPathResource(javaProject.getProject());
         if (sourceResource != null && sourceResource.exists()) {
            IJavaElement javaElement = JavaCore.create(sourceResource);
            if (javaElement != null) {
               return Collections.singletonList(javaElement);
            }
            else {
               return null;
            }
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addAdditionalContent(IJavaProject javaProject, DependencyAnalyzer analyzer) throws CoreException {
      try {
         if (bootClassPath) {
            KeYEnvironment<?> environment = KeYEnvironment.load(KeYExampleUtil.getExampleProof(), null, null, null);
            try {
               // Add KeYJavaType from the original boot class path to the DependencyAnalyzer
               for (KeYJavaType kjt : environment.getJavaInfo().getAllKeYJavaTypes()) {
                  de.uka.ilkd.key.java.abstraction.Type javaType = kjt.getJavaType();
                  if (javaType instanceof ClassDeclaration || javaType instanceof InterfaceDeclaration) {
                     IType jdtType = javaProject.findType(javaType.getFullName());
                     if (jdtType != null) { // Types like '<Default>' are ignored.
                        ASTNode ast = JDTUtil.parse(jdtType.getCompilationUnit());
                        if (ast == null) {
                           if (jdtType.getClassFile().getSource() != null) {
                              ast = JDTUtil.parse(jdtType.getClassFile());
                           }
                           else {
                              List<String> container = JDTUtil.getJavaContainerDescriptions(javaProject);
                              throw new IllegalStateException("The 'Boot Class Path' option can only be used if the JRE source code is available.\n" + 
                                                              "This is currently not the case for: " + CollectionUtil.toString(container) + "\n\n" +
                                                              "May configure project '" + javaProject.getElementName() + "' to use a JDK. ");
                           }
                        }
                        // Search elements
                        SearchVisitor search = new SearchVisitor(environment.getJavaInfo(), kjt);
                        ast.accept(search);
                        assert search.getTypeBinding() != null : "Can't resolve type '" + javaType.getFullName() + "'.";
                        // Ensure that type exists
                        Type type = analyzer.ensureTypeExists(search.getTypeBinding());
                        type.setSource(false); // Ensure that stubs are generated
                        // Ensure that constructors and methods exist
                        for (IMethodBinding constructorBinding : search.getMethodBindings()) {
                           analyzer.ensureMethodExist(constructorBinding);
                        }
                     }
                  }
               }
            }
            finally {
               environment.dispose();
            }
         }
      }
      catch (Exception e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }      
   }
   
   /**
    * Utility classed used to find members of a {@link KeYJavaType} in an
    * AST of JDT.
    * @author Martin Hentschel
    */
   protected static final class SearchVisitor extends ASTVisitor {
      /**
       * The name of the type to search.
       */
      private final String typeFullNamme;
      
      /**
       * The method signatures to search.
       */
      private final Set<MethodSignature> methodSignatures = new HashSet<MethodSignature>();
      
      /**
       * The found {@link ITypeBinding}.
       */
      private ITypeBinding typeBinding;
      
      /**
       * The found {@link IMethodBinding}s.
       */
      private final List<IMethodBinding> methodBindings = new LinkedList<IMethodBinding>();

      /**
       * Constructor.
       * @param javaInfo The {@link JavaInfo}.
       * @param kjt The {@link KeYJavaType} of interest.
       */
      public SearchVisitor(JavaInfo javaInfo, KeYJavaType kjt) {
         // Compute type name of interest
         this.typeFullNamme = kjt.getFullName();
         // Compute constructors of interest
         ImmutableList<IProgramMethod> constructors = javaInfo.getConstructors(kjt);
         for (IProgramMethod pm : constructors) {
            if (!KeYTypeUtil.isImplicitConstructor(pm)) {
               registerProgramMethod(pm);
            }
         }
         // Compute methods of interest
         ImmutableList<IProgramMethod> methods = javaInfo.getAllProgramMethodsLocallyDeclared(kjt);
         for (IProgramMethod pm : methods) {
            registerProgramMethod(pm);
         }
      }
      
      /**
       * Adds the given {@link IProgramMethod} to {@link #methodSignatures}.
       * @param pm The {@link IProgramMethod} to add.
       */
      protected void registerProgramMethod(IProgramMethod pm) {
         ImmutableArray<ParameterDeclaration> parameters = pm.getParameters();
         String[] parameterTypes = new String[parameters.size()];
         for (int i = 0; i < parameterTypes.length; i++) {
            parameterTypes[i] = parameters.get(i).getTypeReference().getKeYJavaType().getFullName();
         }
         this.methodSignatures.add(new MethodSignature(pm.getFullName(), parameterTypes));
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean visit(TypeDeclaration node) {
         ITypeBinding typeBinding = node.resolveBinding();
         if (typeFullNamme.equals(typeBinding.getQualifiedName())) {
            this.typeBinding = typeBinding;
         }
         return super.visit(node);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean visit(MethodDeclaration node) {
         IMethodBinding methodBinding = node.resolveBinding();
         if (methodSignatures.remove(new MethodSignature(methodBinding))) {
            methodBindings.add(methodBinding);
         }
         return super.visit(node);
      }

      /**
       * Returns the found {@link ITypeBinding}.
       * @return The found {@link ITypeBinding} or {@code null} if non was found.
       */
      public ITypeBinding getTypeBinding() {
         return typeBinding;
      }
      
      /**
       * Returns the found {@link IMethodBinding}s.
       * @return The found found {@link IMethodBinding}s.
       */
      public List<IMethodBinding> getMethodBindings() {
         return methodBindings;
      }

      /**
       * Represents a method signature.
       * @author Martin Hentschel
       */
      protected static class MethodSignature {
         /**
          * The name of the method.
          */
         private final String name;
         
         /**
          * The parameters of the method.
          */
         private final ImmutableArray<String> parameterFullTypeNames;

         /**
          * Constructor.
          * @param name The name of the method.
          * @param parameterFullTypeNames The parameters of the method.
          */
         public MethodSignature(String name, String... parameterFullTypeNames) {
            this.name = name;
            this.parameterFullTypeNames = new ImmutableArray<String>(parameterFullTypeNames);
         }

         /**
          * Constructor
          * @param methodBinding The {@link IMethodBinding} to represent.
          */
         public MethodSignature(IMethodBinding methodBinding) {
            this.name = methodBinding.getName();
            ITypeBinding[] parameters = methodBinding.getParameterTypes();
            String[] parameterNames = new String[parameters.length];
            for (int i = 0; i < parameters.length; i++) {
               parameterNames[i] = parameters[i].getQualifiedName();
            }
            this.parameterFullTypeNames = new ImmutableArray<String>(parameterNames);
         }

         /**
          * {@inheritDoc}
          */
         @Override
         public int hashCode() {
            int hashcode = 5;
            hashcode = hashcode * 17 + name.hashCode();
            hashcode = hashcode * 17 + parameterFullTypeNames.hashCode();
            return hashcode;
         }

         /**
          * {@inheritDoc}
          */
         @Override
         public boolean equals(Object obj) {
            if (obj == this) {
               return true;
            }

            if (obj == null || obj.getClass() != getClass() || hashCode() != obj.hashCode()) {
               return false;
            }

            final MethodSignature other = (MethodSignature) obj;
            return name.equals(other.name) &&
                   parameterFullTypeNames.equals(other.parameterFullTypeNames);
         }
      }
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
      catch (Exception e) {
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
                  parent = parent.getParent();
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
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getIgnoreReason(IJavaProject javaProject, 
                                 String stubFolderPath, 
                                 Type abstractType) throws CoreException {
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
   public boolean canSupportGenerics(IJavaProject javaProject, DependencyModel dependencyModel) {
      return !classPath && !bootClassPath;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stubFilesGenerated(IJavaProject javaProject, String stubFolderPath) throws CoreException {
      IProject project = javaProject.getProject();
      final String fullPath = KeYStubGenerationCustomization.computeFullPath(project, stubFolderPath);
      // Ensure that class path is correct according to classPath.
      List<KeYPathEntry> entries = KeYResourceProperties.getClassPathEntries(project);
      KeYPathEntry entry = KeYResourceProperties.searchClassPathEntry(entries, KeYPathEntryKind.WORKSPACE, fullPath);
      if (classPath) {
         if (entry == null) {
            entry = new KeYPathEntry(KeYPathEntryKind.WORKSPACE, fullPath);
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
