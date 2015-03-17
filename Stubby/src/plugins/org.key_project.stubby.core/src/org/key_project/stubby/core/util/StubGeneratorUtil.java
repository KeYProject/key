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
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
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
import org.key_project.util.jdt.JDTUtil;
import org.osgi.framework.Bundle;

/**
 * This class provides utility methods for stub generation.
 * @author Martin Hentschel
 */
public final class StubGeneratorUtil {
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
   public static final String STUB_FOLDER_NAME = "stubs";

   /**
    * Forbid instances by this private constructor.
    */
   private StubGeneratorUtil() {
   }
   
   /**
    * Generates stubs for the given {@link IJavaProject}.
    * @param project The {@link IJavaProject} to generate stubs for.
    */
   public static void generateStubs(IJavaProject project) throws CoreException {
      try {
         // Create dependency model
         DependencyModel dependencyModel = createDependencyModel(project);
         // Save dependency model in project
         if (SAVE_DEPENDENCY_MODEL) {
            IFile emfFile = project.getProject().getFile("Dependencymodel." + DEPENDENCY_MODEL_FILE_EXTENSION);
            ResourceSet rst = new ResourceSetImpl();
            Resource resource = rst.createResource(URI.createPlatformResourceURI(emfFile.getFullPath().toString(), true));
            resource.getContents().add(dependencyModel);
            resource.save(Collections.EMPTY_MAP);
         }
         // Generate stubs with help of JET
         generateFiles(dependencyModel, project);
      }
      catch (IOException e) {
         throw new CoreException(new Status(IStatus.ERROR, "BUNDLE_ID", e.getMessage(), e));
      }
   }
   
   /**
    * Creates the {@link DependencyModel} of the given {@link IJavaProject}.
    * @param project The {@link IJavaProject} to create its {@link DependencyModel}.
    * @return The {@link DependencyModel} or {@code null} if no {@link IJavaProject} was given.
    * @throws CoreException Occurred Exception.
    */
   public static DependencyModel createDependencyModel(IJavaProject project) throws CoreException {
      if (project != null) {
         // Find compilation units in source folders
         List<IPackageFragmentRoot> sourceFolders = JDTUtil.getSourceFolders(project);
         List<ICompilationUnit> compilationUnits = JDTUtil.listCompilationUnit(sourceFolders);
         // Create dependency model
         DependencyModel dependencyModel = DependencymodelFactory.eINSTANCE.createDependencyModel();
         DependencyAnalyzer analyzer = new DependencyAnalyzer();
         for (ICompilationUnit unit : compilationUnits) {
            ASTNode ast = JDTUtil.parse(unit);
            if (ast != null) {
               ast.accept(analyzer);
            }
         }
         dependencyModel.getTypes().addAll(analyzer.getOuterTypes());
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
    * @throws CoreException Occurred Exception.
    */
   private static void generateFiles(DependencyModel dependencyModel, IJavaProject javaProject) throws CoreException {
      if (dependencyModel != null && JDTUtil.isJavaProject(javaProject)) {
         for (AbstractType abstractType : dependencyModel.getTypes()) {
            if (abstractType instanceof Type && !abstractType.isSource()) {
               generateType((Type) abstractType, javaProject.getProject());
            }
         }
      }
   }
   
   /**
    * Generates the stub file for the given {@link Type}.
    * @param type The {@link Type} to generate its stub file.
    * @param stubProject The target {@link IJavaProject}.
    * @return The created or updated {@link IFile}.
    * @throws CoreException Occurred Exception.
    */
   public static IFile generateType(Type type, IProject stubProject) throws CoreException {
      // Create new content
      TypeTemplate template = new TypeTemplate();
      String content = template.generate(type);
      // Save file
      String projectStubFolder = STUB_FOLDER_NAME;
      String[] res = type.getPackage().split("\\.");
      String projectSimpleName = type.getSimpleName() + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT;  
      IFolder stubFolder = stubProject.getFolder(projectStubFolder);
      if (!stubFolder.exists()) { 
         stubFolder.create(true, true, null);
      }
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
}
