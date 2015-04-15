package org.key_project.stubby.core.util;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.emf.codegen.merge.java.JControlModel;
import org.eclipse.emf.codegen.merge.java.JMerger;
import org.eclipse.emf.codegen.merge.java.facade.FacadeHelper;
import org.eclipse.emf.codegen.merge.java.facade.ast.ASTFacadeHelper;
import org.eclipse.emf.codegen.util.CodeGenUtil;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.dom.ASTNode;
import org.key_project.stubby.core.Activator;
import org.key_project.stubby.core.customization.IGeneratorCustomization;
import org.key_project.stubby.core.jdt.DependencyAnalyzer;
import org.key_project.stubby.core.template.TypeTemplate;
import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.stubby.model.dependencymodel.DependencymodelFactory;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.osgi.framework.Bundle;

/**
 * This class provides utility methods for stub generation.
 * @author Martin Hentschel
 */
public final class StubGeneratorUtil {
   /**
    * {@link IProject#getPersistentProperties()} key for the stub folder.
    */
   public static final QualifiedName STUB_FOLDER_PATH = new QualifiedName("org.key_project.stubby.core", "stubFolder");
   
   /**
    * Indicates if the dependency model should be saved during stub generation.
    */
   public static final boolean SAVE_DEPENDENCY_MODEL = false;
   
   /**
    * The file extension used to store dependency models.
    */
   public static final String DEPENDENCY_MODEL_FILE_EXTENSION = "dependencymodel";
   
   /**
    * The name of the folder in an {@link IProject} which will contain the generated stubs.
    */
   public static final String DEFAULT_STUB_FOLDER_PATH = "stubs";

   /**
    * Forbid instances by this private constructor.
    */
   private StubGeneratorUtil() {
   }
   
   /**
    * Generates stubs for the given {@link IJavaProject}.
    * @param project The {@link IJavaProject} to generate stubs for.
    * @param stubFolderPath The path to the stub folder.
    * @param monitor The {@link IProgressMonitor} to use.
    * @param customizations Optional {@link IGeneratorCustomization} to consider.
    * @return All ignored types including the reason why.
    */
   public static List<IgnoredType> generateStubs(IJavaProject project, 
                                                 String stubFolderPath,
                                                 IProgressMonitor monitor,
                                                 IGeneratorCustomization... customizations) throws CoreException {
      try {
         if (monitor == null) {
            monitor = new NullProgressMonitor();
         }
         // Create dependency model
         DependencyModel dependencyModel = createDependencyModel(project, monitor, customizations);
         // Inform customizations
         for (IGeneratorCustomization customization : customizations) {
            customization.dependencyModelCreated(project, stubFolderPath, dependencyModel);
         }
         // Save dependency model in project
         if (SAVE_DEPENDENCY_MODEL) {
            SWTUtil.checkCanceled(monitor);
            monitor.beginTask("Saving dependency model", IProgressMonitor.UNKNOWN);
            IFile emfFile = project.getProject().getFile("Dependencymodel." + DEPENDENCY_MODEL_FILE_EXTENSION);
            ResourceSet rst = new ResourceSetImpl();
            Resource resource = rst.createResource(URI.createPlatformResourceURI(emfFile.getFullPath().toString(), true));
            resource.getContents().add(dependencyModel);
            resource.save(Collections.EMPTY_MAP);
            monitor.done();
         }
         // Generate stubs with help of JET
         List<IgnoredType> ignoredTypes = generateFiles(dependencyModel, project, stubFolderPath, monitor, customizations);
         // Inform customizations
         for (IGeneratorCustomization customization : customizations) {
            customization.stubFilesGenerated(project, stubFolderPath);
         }
         return ignoredTypes;
      }
      catch (IOException e) {
         throw new CoreException(new Status(IStatus.ERROR, Activator.BUNDLE_ID, e.getMessage(), e));
      }
   }
   
   /**
    * Creates the {@link DependencyModel} of the given {@link IJavaProject}.
    * @param project The {@link IJavaProject} to create its {@link DependencyModel}.
    * @param monitor The {@link IProgressMonitor} to use.
    * @param customizations Optional {@link IGeneratorCustomization} to consider.
    * @return The {@link DependencyModel} or {@code null} if no {@link IJavaProject} was given.
    * @throws CoreException Occurred Exception.
    */
   public static DependencyModel createDependencyModel(IJavaProject project, 
                                                       IProgressMonitor monitor,
                                                       IGeneratorCustomization... customizations) throws CoreException {
      try {
         if (monitor == null) {
            monitor = new NullProgressMonitor();
         }
         if (project != null) {
            // Check if specific IJavaElements are given.
            List<? extends IJavaElement> sourceFolders = null;
            int i = 0;
            while (sourceFolders == null && i < customizations.length) {
               sourceFolders = customizations[i].defineSources(project);
               i++;
            }
            if (sourceFolders == null) {
               sourceFolders = JDTUtil.getSourceFolders(project);
            }
            // Find compilation units in source folders
            monitor.beginTask("Listing source files", IProgressMonitor.UNKNOWN);
            List<ICompilationUnit> compilationUnits = JDTUtil.listCompilationUnit(sourceFolders);
            monitor.done();
            // Analyze dependencies of found source files
            monitor.beginTask("Analyzing dependencies", compilationUnits.size());
            DependencyModel dependencyModel = DependencymodelFactory.eINSTANCE.createDependencyModel();
            DependencyAnalyzer analyzer = new DependencyAnalyzer();
            for (ICompilationUnit unit : compilationUnits) {
               SWTUtil.checkCanceled(monitor);
               ASTNode ast = JDTUtil.parse(unit);
               if (ast != null) {
                  ast.accept(analyzer);
               }
               monitor.worked(1);
            }
            monitor.done();
            // Inform customizations
            if (!ArrayUtil.isEmpty(customizations)) {
               monitor.beginTask("Adding additional content", IProgressMonitor.UNKNOWN);
               for (IGeneratorCustomization customization : customizations) {
                  customization.addAdditionalContent(project, analyzer);
               }
               monitor.done();
            }
            // Create dependency model
            monitor.beginTask("Creating dependency model", IProgressMonitor.UNKNOWN);
            dependencyModel.getTypes().addAll(analyzer.getOuterTypes());
            monitor.done();
            return dependencyModel;
         }
         else {
            return null;
         }
      }
      catch (OperationCanceledException e) {
         throw e;
      }
      catch (RuntimeException e) {
         throw new CoreException(new Status(IStatus.ERROR, Activator.BUNDLE_ID, e.getMessage(), e));
      }
   }

   /**
    * Generates the stub files for all non source {@link Type}s of the given {@link DependencyModel}.
    * @param dependencyModel The {@link DependencyModel}.
    * @param javaProject The target {@link IJavaProject}.
    * @param stubFolderPath The path to the stub folder.
    * @param monitor The {@link IProgressMonitor} to use.
    * @param customizations Optional {@link IGeneratorCustomization} to consider.
    * @return All ignored types including the reason why.
    * @throws CoreException Occurred Exception.
    */
   private static List<IgnoredType> generateFiles(DependencyModel dependencyModel, 
                                                  IJavaProject javaProject, 
                                                  String stubFolderPath,
                                                  IProgressMonitor monitor,
                                                  IGeneratorCustomization... customizations) throws CoreException {
      // Ensure that stub folder exists
      IFolder stubFolder = javaProject.getProject().getFolder(new Path(stubFolderPath));
      if (!stubFolder.exists() || ArrayUtil.isEmpty(stubFolder.members())) {
         ResourceUtil.ensureExists(stubFolder);
         for (IGeneratorCustomization customization : customizations) {
            customization.stubFolderCreated(stubFolder);
         }
      }
      // Check if generics should be included
      boolean genericFree = false;
      int i = 0;
      while (!genericFree && i < customizations.length) {
         if (!customizations[i].canSupportGenerics(javaProject, dependencyModel)) {
            genericFree = true;
         }
         i++;
      }
      // Generate files
      List<IgnoredType> ignoredTypes = new LinkedList<IgnoredType>();
      if (dependencyModel != null && JDTUtil.isJavaProject(javaProject)) {
         monitor.beginTask("Creating stub files", dependencyModel.getTypes().size());
         for (Type type : dependencyModel.getTypes()) {
            SWTUtil.checkCanceled(monitor);
            if (!type.isSource()) {
               String ignoreReason = null;
               for (int j = 0; ignoreReason == null && j < customizations.length; j++) {
                  ignoreReason = customizations[j].getIgnoreReason(javaProject, stubFolderPath, type);
               }
               if (ignoreReason == null) {
                  generateType(type, genericFree, javaProject.getProject(), stubFolderPath);
               }
               else {
                  ignoredTypes.add(new IgnoredType(type, ignoreReason));
               }
            }
            monitor.worked(1);
         }
         monitor.done();
      }
      return ignoredTypes;
   }
   
   /**
    * Generates the stub file for the given {@link Type}.
    * @param type The {@link Type} to generate its stub file.
    * @param genericFree If {@code true} generated stubs are generic free, otherwise generics might be contained.
    * @param stubProject The target {@link IJavaProject}.
    * @param stubFolderPath The path to the stub folder.
    * @return The created or updated {@link IFile}.
    * @throws CoreException Occurred Exception.
    */
   public static IFile generateType(Type type, 
                                    boolean genericFree,
                                    IProject stubProject, 
                                    String stubFolderPath) throws CoreException {
      // Create new content
      String content = generateContent(type, genericFree);
      // Save file
      String[] res = type.getPackage().split("\\.");
      String projectSimpleName = type.getSimpleName() + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT;  
      IFolder stubFolder = stubProject.getFolder(new Path(stubFolderPath));
      ResourceUtil.ensureExists(stubFolder);
      for (String stubSub : res) {
         stubFolder = stubFolder.getFolder(stubSub);
         if (!stubFolder.exists()) {
            stubFolder.create(true, true, null);
         }
      }
      IFile stubJavaClass = stubFolder.getFile(projectSimpleName);
      if (!stubJavaClass.exists()) {
         // Create file
         stubJavaClass.create(new ByteArrayInputStream(content.getBytes()), true, null);
      }
      else {
         // Merge new with existing content
         JControlModel controlModel = new JControlModel();
         controlModel.setConvertToStandardBraceStyle(true);
         FacadeHelper facadeHelper = CodeGenUtil.instantiateFacadeHelper(ASTFacadeHelper.class.getName()); // The JDOMFacadeHelper can not parser constructors ending with ';' instead by a body.
         controlModel.initialize(facadeHelper, getStubbyMergeURI());
         JMerger merger = new JMerger(controlModel);
         merger.setSourceCompilationUnit(merger.createCompilationUnitForContents(content));
         merger.setTargetCompilationUnit(merger.createCompilationUnitForInputStream(stubJavaClass.getContents()));
         merger.merge();
         content = merger.getTargetCompilationUnitContents();
         // Modify file
         stubJavaClass.setContents(new ByteArrayInputStream(content.getBytes()), true, true, null);
      }
      return stubJavaClass;
   }
   
   /**
    * Generates the java stub source code of the given {@link Type}.
    * @param type The {@link Type}.
    * @param genericFree If {@code true} generated stubs are generic free, otherwise generics might be contained.
    * @return The generated java stub source code.
    */
   public static String generateContent(Type type, boolean genericFree) {
      TypeTemplate template = new TypeTemplate(genericFree);
      return template.generate(type);
   }

   /**
    * Returns the URL of the given merge rules.
    * @return The URL of the given merge rules.
    */
   public static String getStubbyMergeURI() {
      Bundle bundle = Platform.getBundle(Activator.BUNDLE_ID);
      URL url = bundle.getEntry("jmerge/stubby-merge.xml");
      return url.toString();
   }
   
   /**
    * Returns the stub folder of the given {@link IJavaProject}.
    * @param javaProject The {@link IJavaProject}.
    * @return The stub folder.
    */
   public static String getStubFolderPath(IJavaProject javaProject) {
      return getStubFolderPath(javaProject.getProject());
   }
   
   /**
    * Returns the stub folder of the given {@link IProject}.
    * @param project The {@link IProject}.
    * @return The stub folder.
    */
   public static String getStubFolderPath(IProject project) {
      try {
         String value = project.getPersistentProperty(STUB_FOLDER_PATH);
         if (!StringUtil.isEmpty(value)) {
            return value;
         }
         else {
            return DEFAULT_STUB_FOLDER_PATH;
         }
      }
      catch (CoreException e) {
         return DEFAULT_STUB_FOLDER_PATH;
      }
   }
   
   /**
    * Sets the stub folder of the given {@link IJavaProject}.
    * @param javaProject The {@link IJavaProject} to set its stub folder.
    * @param stubFolder The stub folder to set.
    * @throws CoreException Occurred Exception.
    */
   public static void setStubFolderPath(IJavaProject javaProject, String stubFolder) throws CoreException {
      setStubFolderPath(javaProject.getProject(), stubFolder);
   }
   
   /**
    * Sets the stub folder of the given {@link IProject}.
    * @param project The {@link IProject} to set its stub folder.
    * @param stubFolder The stub folder to set.
    * @throws CoreException Occurred Exception.
    */
   public static void setStubFolderPath(IProject project, String stubFolder) throws CoreException {
      project.setPersistentProperty(STUB_FOLDER_PATH, stubFolder);
   }
   
   public static final class IgnoredType {
      private final Type type;
      
      private final String reason;

      public IgnoredType(Type type, String reason) {
         this.type = type;
         this.reason = reason;
      }

      public Type getType() {
         return type;
      }

      public String getReason() {
         return reason;
      }
   }
}
