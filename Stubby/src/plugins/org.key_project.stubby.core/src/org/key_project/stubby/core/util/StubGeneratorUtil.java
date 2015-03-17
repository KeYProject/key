package org.key_project.stubby.core.util;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.emf.codegen.merge.java.JControlModel;
import org.eclipse.emf.codegen.merge.java.JMerger;
import org.eclipse.emf.codegen.merge.java.facade.FacadeHelper;
import org.eclipse.emf.codegen.merge.java.facade.jdom.JDOMFacadeHelper;
import org.eclipse.emf.codegen.util.CodeGenUtil;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.dom.ASTNode;
import org.key_project.stubby.core.Activator;
import org.key_project.stubby.core.jdt.DependencyAnalyzer;
import org.key_project.stubby.core.template.TypeTemplate;
import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.stubby.model.dependencymodel.DependencymodelFactory;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
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
    */
   public static void generateStubs(IJavaProject project, 
                                    String stubFolderPath,
                                    IProgressMonitor monitor) throws CoreException {
      try {
         if (monitor == null) {
            monitor = new NullProgressMonitor();
         }
         // Create dependency model
         DependencyModel dependencyModel = createDependencyModel(project, monitor);
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
         generateFiles(dependencyModel, project, stubFolderPath, monitor);
      }
      catch (IOException e) {
         throw new CoreException(new Status(IStatus.ERROR, "BUNDLE_ID", e.getMessage(), e));
      }
   }
   
   /**
    * Creates the {@link DependencyModel} of the given {@link IJavaProject}.
    * @param project The {@link IJavaProject} to create its {@link DependencyModel}.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The {@link DependencyModel} or {@code null} if no {@link IJavaProject} was given.
    * @throws CoreException Occurred Exception.
    */
   public static DependencyModel createDependencyModel(IJavaProject project, IProgressMonitor monitor) throws CoreException {
      if (monitor == null) {
         monitor = new NullProgressMonitor();
      }
      if (project != null) {
         // Find compilation units in source folders
         monitor.beginTask("Listing source files", IProgressMonitor.UNKNOWN);
         List<IPackageFragmentRoot> sourceFolders = JDTUtil.getSourceFolders(project);
         List<ICompilationUnit> compilationUnits = JDTUtil.listCompilationUnit(sourceFolders);
         monitor.done();
         // Create dependency model
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
         monitor.beginTask("Creating dependency model", IProgressMonitor.UNKNOWN);
         dependencyModel.getTypes().addAll(analyzer.getOuterTypes());
         monitor.done();
         return dependencyModel;
      }
      else {
         return null;
      }
   }

   /**
    * Generates the stub files for all non source {@link Type}s of the given {@link DependencyModel}.
    * @param dependencyModel The {@link DependencyModel}.
    * @param javaProject The target {@link IJavaProject}.
    * @param stubFolderPath The path to the stub folder.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws CoreException Occurred Exception.
    */
   private static void generateFiles(DependencyModel dependencyModel, 
                                     IJavaProject javaProject, 
                                     String stubFolderPath,
                                     IProgressMonitor monitor) throws CoreException {
      if (dependencyModel != null && JDTUtil.isJavaProject(javaProject)) {
         monitor.beginTask("Creating stub files", dependencyModel.getTypes().size());
         for (AbstractType abstractType : dependencyModel.getTypes()) {
            SWTUtil.checkCanceled(monitor);
            if (abstractType instanceof Type && !abstractType.isSource()) {
               generateType((Type) abstractType, javaProject.getProject(), stubFolderPath);
            }
            monitor.worked(1);
         }
         monitor.done();
      }
   }
   
   /**
    * Generates the stub file for the given {@link Type}.
    * @param type The {@link Type} to generate its stub file.
    * @param stubProject The target {@link IJavaProject}.
    * @param stubFolderPath The path to the stub folder.
    * @return The created or updated {@link IFile}.
    * @throws CoreException Occurred Exception.
    */
   public static IFile generateType(Type type, 
                                    IProject stubProject, 
                                    String stubFolderPath) throws CoreException {
      // Create new content
      TypeTemplate template = new TypeTemplate();
      String content = template.generate(type);
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
         FacadeHelper facadeHelper = CodeGenUtil.instantiateFacadeHelper(JDOMFacadeHelper.class.getName()); // The default class JMerger.DEFAULT_FACADE_HELPER_CLASS drops non Javadoc comments
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
}
