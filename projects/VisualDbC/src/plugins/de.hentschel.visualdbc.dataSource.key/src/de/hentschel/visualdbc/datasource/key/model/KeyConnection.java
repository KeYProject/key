/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.key.model;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.util.eclipse.ResourceUtil;
import org.key_project.key4eclipse.util.java.ArrayUtil;
import org.key_project.key4eclipse.util.java.ObjectUtil;
import org.key_project.key4eclipse.util.java.SwingUtil;
import org.key_project.key4eclipse.util.java.thread.AbstractRunnableWithException;
import org.key_project.key4eclipse.util.java.thread.IRunnableWithException;

import de.hentschel.visualdbc.datasource.key.intern.helper.KeyHacks;
import de.hentschel.visualdbc.datasource.key.intern.helper.OpenedProof;
import de.hentschel.visualdbc.datasource.key.util.LogUtil;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSContainer;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryAttribute;
import de.hentschel.visualdbc.datasource.model.memory.MemoryClass;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnection;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConstructor;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInterface;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInvariant;
import de.hentschel.visualdbc.datasource.model.memory.MemoryMethod;
import de.hentschel.visualdbc.datasource.model.memory.MemoryPackage;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.OperationContract;

/**
 * Implementation for {@link IDSConnection} to analyze code files with KeY.
 * @author Martin Hentschel
 */
public class KeyConnection extends MemoryConnection {
   /**
    * Key word: void
    */
   public static final String VOID = "void";

   /**
    * Separates parameters in signatures.
    */
   public static final String PARAMETER_SEPARATOR = ", ";

   /**
    * Separates the variable name from his type.
    */
   public static final String VAR_NAME_TYPE_SEPARATOR = " : ";

   /**
    * The start of signature parameters.
    */
   public static final String PARAMETER_START = "(";

   /**
    * The end of signature parameters.
    */
   public static final String PARAMETER_END = ")";

   /**
    * Array declaration
    */
   public static final String ARRAY_DECLARATION = "[]";

   /**
    * Separator between packages and types.
    */
   public static final String PACKAGE_SEPARATOR = ".";
   
   /**
    * The name of implicit constructors.
    */
   public static final String INIT_NAME = ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER;

   /**
    * The name of the proof obligation used for operation contracts.
    */
   public static final String PROOF_OBLIGATION_OPERATION_CONTRACT = "ContractPO";
   
   /**
    * The opened KeY model represented as {@link InitConfig}.
    */
   private InitConfig initConfig;

   /**
    * The used {@link ProblemInitializer}.
    */
   private ProblemInitializer init;
   
   /**
    * The used {@link MainWindow}.
    */
   private MainWindow main;
   
   /**
    * Maps all {@link ProgramMethod}s to their data source instance.
    */
   private Map<ProgramMethod, IDSOperation> operationsMapping;

   /**
    * Maps all {@link OperationContract}s to their data source instance.
    */
   private Map<OperationContract, IDSOperationContract> operationContractsMapping;
   
   /**
    * Maps all {@link ClassInvariant}s to their data source instance.
    */
   private Map<ClassInvariant, IDSInvariant> invariantsMapping;
   
   /**
    * Maps all {@link KeYJavaType}s to their data source instance.
    */
   private Map<KeYJavaType, IDSType> typesMapping;
   
   /**
    * The used listener to observe {@link #main}.
    */
   private GUIListener mainGuiListener = new GUIListener() {
      @Override
      public void shutDown(GUIEvent e) {
         handleMainClosed(e);
      }
      
      @Override
      public void modalDialogOpened(GUIEvent e) {
      }
      
      @Override
      public void modalDialogClosed(GUIEvent e) {
      }
   };
   
   /**
    * Constructor.
    * @param driver The {@link IDSDriver} that has created this connection.
    */
   public KeyConnection(IDSDriver driver) {
      super(driver);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void connect(Map<String, Object> connectionSettings, 
                       final boolean interactive,
                       final IProgressMonitor monitor) throws DSException {
      try {
         Assert.isNotNull(connectionSettings);
         // Initialize instance variables
         operationsMapping = new HashMap<ProgramMethod, IDSOperation>();
         operationContractsMapping = new HashMap<OperationContract, IDSOperationContract>();
         invariantsMapping = new HashMap<ClassInvariant, IDSInvariant>();
         typesMapping = new HashMap<KeYJavaType, IDSType>();
         // Get settings
         final File location = getLocation(connectionSettings);
         final List<File> classPathEntries = getClassPathEntries(connectionSettings);
         final File bootClassPath = getBootClassPath(connectionSettings);
         if (location == null || !location.exists()) {
            throw new DSException("The location \"" + location + "\" doesn't exist.");
         }
         final boolean skipLibraryClasses = isSkipLibraryClasses(connectionSettings);
         final DSPackageManagement packageManagement = getPackageManagent(connectionSettings);
         // Instantiate KeY main window
         SwingUtil.invokeAndWait(new Runnable() {
            @Override
            public void run() {
               if (!MainWindow.hasInstance()) {
                  MainWindow.createInstance(Main.getMainWindowTitle());
               }
               // Open connection in key
               if (interactive) {
                  main = MainWindow.getInstance();
                  main.setVisible(true);
               }
               else {
                  main = MainWindow.getInstance(false);
               }
            }
         });
         // Open environment and analyse types
         IRunnableWithException run = new AbstractRunnableWithException() {
            @Override
            public void run() {
               try {
                  KeYMediator mediator = main.getMediator();
                  mediator.addGUIListener(mainGuiListener);
                  ProblemLoader loader = new ProblemLoader(location, classPathEntries, bootClassPath, main);
                  EnvInput envInput = loader.createEnvInput(location, classPathEntries, bootClassPath);
                  init = main.createProblemInitializer();
                  initConfig = init.prepare(envInput);
                  // Analyze classes, interfaces, enums and packages
                  analyzeTypes(initConfig.getServices(), skipLibraryClasses, packageManagement, monitor);
               }
               catch (Exception e) {
                  setException(e);
               }
            }
         };
         SwingUtil.invokeAndWait(run);
         if (run.getException() != null) {
            throw run.getException();
         }
         super.connect(connectionSettings, interactive, monitor);
      }
      catch (DSException e) {
         throw e;
      }
      catch (Exception e) {
         throw new DSException(e);
      }
   }

   /**
    * When the main was closed.
    * @param e The event to handle.
    */
   protected void handleMainClosed(GUIEvent e) {
      try {
         disconnect(false);
      }
      catch (DSException exception) {
         LogUtil.getLogger().logError(exception);
      }
   }

   /**
    * Analyzes the information in the {@link Services} and fills the
    * data connection model.
    * @param services The read {@link Services}.
    * @param skipLibraryClasses {@code true} = skip, {@code false} = include
    * @param packageManagement The package management to use.
    * @throws DSException Occurred Exception
    */
   protected void analyzeTypes(Services services, 
                               boolean skipLibraryClasses,
                               DSPackageManagement packageManagement,
                               IProgressMonitor monitor) throws DSException {
      // get all classes
      final Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
      monitor.beginTask("Filtering types", kjts.size());
      final Iterator<KeYJavaType> it = kjts.iterator();
      while (it.hasNext()) {
         KeYJavaType kjt = it.next();
         if (!(kjt.getJavaType() instanceof ClassDeclaration || 
               kjt.getJavaType() instanceof InterfaceDeclaration) || 
             (((TypeDeclaration)kjt.getJavaType()).isLibraryClass() && skipLibraryClasses)) {
            it.remove();
         }
         monitor.worked(1);
      }
      monitor.done();
      // sort classes alphabetically
      monitor.beginTask("Sorting types", IProgressMonitor.UNKNOWN);
      final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
      Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
         public int compare(KeYJavaType o1, KeYJavaType o2) {
            return o1.getFullName().compareTo(o2.getFullName());
         }
      });
      monitor.done();
      // Fill data connection model
      Map<String, List<MemoryClass>> innerClasses = new HashMap<String, List<MemoryClass>>(); // Contains all inner classes that are added to their parents after analyzing all types to make sure that the parent type already exists as IDSType.
      Map<String, List<MemoryInterface>> innerInterfaces = new HashMap<String, List<MemoryInterface>>(); // Contains all inner classes that are added to their parents after analyzing all types to make sure that the parent type already exists as IDSType.
      Map<String, IDSType> types = new HashMap<String, IDSType>(); // Maps the full name to the created IDSType.
      monitor.beginTask("Analyzing types", kjtsarr.length);
      for (KeYJavaType type : kjtsarr) {
         // Create class
         String typeName = getTypeName(type, packageManagement);
         Assert.isTrue(type.getJavaType() instanceof ClassType);
         ClassType ct = (ClassType)type.getJavaType();
         if (isInner(services, type)) {
            String parentName = getParentName(services, type);
            if (ct.isInterface()) {
               MemoryInterface interfaceInstance = createInterface(services, ct, type, typeName);
               List<MemoryInterface> parentInnerInterfaces = innerInterfaces.get(parentName);
               if (parentInnerInterfaces == null) {
                  parentInnerInterfaces = new LinkedList<MemoryInterface>();
                  innerInterfaces.put(parentName, parentInnerInterfaces);
               }
               parentInnerInterfaces.add(interfaceInstance);
               types.put(type.getFullName(), interfaceInstance);
            }
            else {
               MemoryClass classInstance = createClass(services, ct, type, typeName);
               List<MemoryClass> parentInnerClasses = innerClasses.get(parentName);
               if (parentInnerClasses == null) {
                  parentInnerClasses = new LinkedList<MemoryClass>();
                  innerClasses.put(parentName, parentInnerClasses);
               }
               parentInnerClasses.add(classInstance);
               types.put(type.getFullName(), classInstance);
            }
         }
         else {
            // Check if it is contained in a package
            PackageReference pr = type.createPackagePrefix();
            if (pr != null && !DSPackageManagement.NO_PACKAGES.equals(packageManagement)) {
               // Find package to insert
               IDSPackage dsPackage = getPackage(pr, packageManagement);
               if (ct.isInterface()) {
                  MemoryInterface interfaceInstance = createInterface(services, ct, type, typeName);
                  interfaceInstance.setParentContainer(dsPackage);
                  dsPackage.getInterfaces().add(interfaceInstance);
                  types.put(type.getFullName(), interfaceInstance);
               }
               else {
                  MemoryClass classInstance = createClass(services, ct, type, typeName);
                  classInstance.setParentContainer(dsPackage);
                  dsPackage.getClasses().add(classInstance);
                  types.put(type.getFullName(), classInstance);
               }
            }
            else {
               if (ct.isInterface()) {
                  MemoryInterface interfaceInstance = createInterface(services, ct, type, typeName);
                  interfaceInstance.setParentContainer(this);
                  getInterfaces().add(interfaceInstance);
                  types.put(type.getFullName(), interfaceInstance);
               }
               else {
                  MemoryClass classInstance = createClass(services, ct, type, typeName);
                  classInstance.setParentContainer(this);
                  getClasses().add(classInstance);
                  types.put(type.getFullName(), classInstance);
               }
            }
         }
         monitor.worked(1);
      }
      monitor.done();
      // Add inner classes to their parents
      monitor.beginTask("Adding inner classes", innerClasses.size());
      Set<Entry<String, List<MemoryClass>>> innerClassEntries = innerClasses.entrySet();
      for (Entry<String, List<MemoryClass>> innerEntry : innerClassEntries) {
         IDSType parent = types.get(innerEntry.getKey());
         Assert.isNotNull(parent);
         List<MemoryClass> innerClassList = innerEntry.getValue();
         Assert.isNotNull(innerClassList);
         for (MemoryClass innerClass : innerClassList) {
            parent.getInnerClasses().add(innerClass);
            innerClass.setParentType(parent);
         }
         monitor.worked(1);
      }
      monitor.done();
      // Add inner interfaces to their parents
      monitor.beginTask("Adding inner interfaces", innerInterfaces.size());
      Set<Entry<String, List<MemoryInterface>>> innerInterfaceEntries = innerInterfaces.entrySet();
      for (Entry<String, List<MemoryInterface>> innerEntry : innerInterfaceEntries) {
         IDSType parent = types.get(innerEntry.getKey());
         Assert.isNotNull(parent);
         List<MemoryInterface> innerInterfaceList = innerEntry.getValue();
         Assert.isNotNull(innerInterfaceList);
         for (MemoryInterface innerInterface : innerInterfaceList) {
            parent.getInnerInterfaces().add(innerInterface);
            innerInterface.setParentType(parent);
         }
         monitor.worked(1);
      }
      // Set parent dependencies
      Collection<IDSType> modelTypes = types.values();
      monitor.beginTask("Adding parent references", modelTypes.size());
      for (IDSType type : modelTypes) {
         if (type instanceof IDSClass) {
            IDSClass classInstance = (IDSClass)type;
            for (String parent : classInstance.getExtendsFullnames()) {
               IDSType parentInstance = types.get(parent);
               if (parentInstance != null) {
                  Assert.isTrue(parentInstance instanceof IDSClass); 
                  classInstance.getExtends().add((IDSClass)parentInstance);
               }
            }
            for (String parent : classInstance.getImplementsFullnames()) {
               IDSType parentInstance = types.get(parent);
               if (parentInstance != null) {
                  Assert.isTrue(parentInstance instanceof IDSInterface); 
                  classInstance.getImplements().add((IDSInterface)parentInstance);
               }
            }
         }
         else if (type instanceof IDSInterface) {
            IDSInterface interfaceInstance = (IDSInterface)type;
            for (String parent : interfaceInstance.getExtendsFullnames()) {
               IDSType parentInstance = types.get(parent);
               if (parentInstance != null) {
                  Assert.isTrue(parentInstance instanceof IDSInterface); 
                  interfaceInstance.getExtends().add((IDSInterface)parentInstance);
               }
            }
         }
         else {
            throw new DSException("Unknown model type: " + type);
         }
         monitor.worked(1);
      }
      monitor.done();
   }

   /**
    * Checks if the given type is an inner or anonymous type.
    * @param services The {@link Services} to use.
    * @param type The type to check.
    * @return {@code true} is inner or anonymous, {@code false} is not
    */
   protected boolean isInner(Services services, KeYJavaType type) {
      String parentName = getParentName(services, type);
      if (parentName != null) {
         return !services.getJavaInfo().isPackage(parentName);
      }
      else {
         return false; // Normal class in default package
      }
   }
   
   /**
    * Returns the name of the parent package/type or {@code null} if it has no one.
    * @param services The {@link Services} to use.
    * @param type The type.
    * @return The parent package/type or {@code null} if it has no one.
    */
   protected String getParentName(Services services, KeYJavaType type) {
      return getParentName(services, type.getFullName());
   }
   
   /**
    * Returns the name of the parent package/type or {@code null} if it has no one.
    * @param services The {@link Services} to use.
    * @param fullName The name of the current package/type.
    * @return The parent package/type or {@code null} if it has no one.
    */
   protected String getParentName(Services services, String fullName) {
      int lastSeparator = fullName.lastIndexOf(PACKAGE_SEPARATOR);
      if (lastSeparator >= 0) {
         String parentName = fullName.substring(0, lastSeparator);
         // Check if parentName is existing package or type (required for anonymous classes that have multiple numbers like ClassContainer.DefaultChildClass.23543334.10115480)
         if (services.getJavaInfo().isPackage(parentName)) {
            return parentName;
         }
         else if (isType(services, parentName)) {
            return parentName;
         }
         else {
            return getParentName(services, parentName);
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Checks if the given full name is a type in KeY.
    * @param services The services to use.
    * @param fullName The full name to check.
    * @return {@code true} = is type, {@code false} = is no type
    */
   protected boolean isType(Services services, String fullName) {
      try {
         KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(fullName); 
         return kjt != null;
      }
      catch (Exception e) {
         return false; // RuntimeException is thrown if type not exist.
      }
   }

   /**
    * <p>
    * Returns the parent package for types based on the {@link DSPackageManagement}.
    * </p>
    * <p>
    * If it not already exist in the diagram model it is created.
    * </p>
    * @param pr The package in KeY to search.
    * @param packageManagement The {@link DSPackageManagement} to use.
    * @return The {@link IDSPackage} in the diagram model.
    * @throws DSException Occurred Exception
    */
   protected IDSPackage getPackage(PackageReference pr, DSPackageManagement packageManagement) throws DSException {
      IDSPackage result = null;
      if (DSPackageManagement.HIERARCHY.equals(packageManagement)) {
         // Hierarchy
         return searchPackageHierarchy(pr, packageManagement);
      }
      else {
         // Flat list
         String packageName = getPackageName(pr, packageManagement);
         result = getPackage(packageName);
         if (result == null) {
            result = createPackage(pr, packageName, this);
            getPackages().add(result);
         }
      }
      return result;
   }
   
   /**
    * <p>
    * Searches recursive the package in the diagram model.
    * </p>
    * <p>
    * If it not already exist in the diagram model it is created.
    * </p>
    * @param pr The package to search.
    * @param packageManagement The {@link DSPackageManagement} to use.
    * @return The {@link IDSPackage} in the diagram model.
    * @throws DSException Occurred Exception
    */
   protected IDSPackage searchPackageHierarchy(PackageReference pr, DSPackageManagement packageManagement) throws DSException {
      PackageReference parent = pr.getPackageReference();
      String packageName = getPackageName(pr, packageManagement);
      if (parent != null) {
         IDSPackage parentInstance = searchPackageHierarchy(parent, packageManagement);
         IDSPackage result = parentInstance.getPackage(packageName);
         if (result == null) {
            result = createPackage(pr, packageName, parentInstance);
            parentInstance.getPackages().add(result);
         }
         return result;
      }
      else {
         IDSPackage result = getPackage(packageName);
         if (result == null) {
            result = createPackage(pr, packageName, this);
            getPackages().add(result);
         }
         return result;
      }
   }
   
   /**
    * Returns the name of package based on the {@link DSPackageManagement}.
    * @param pr The package in KeY.
    * @param packageManagement The {@link DSPackageManagement} to use.
    * @return The package name to use in the diagram model.
    */
   protected String getPackageName(PackageReference pr, DSPackageManagement packageManagement) {
      if (DSPackageManagement.FLAT_LIST.equals(packageManagement)) {
         return pr.toSource();
      }
      else {
         return pr.getName();
      }
   }

   /**
    * Returns the signature of the method.
    * @param method The method.
    * @return The signature.
    */
   protected String getSignature(ProgramMethod method) {
      StringBuffer sb = new StringBuffer();
      sb.append(method.getFullName());
      sb.append(PARAMETER_START);
      sb.append(getSignatureParameters(method));
      sb.append(PARAMETER_END);
      return sb.toString();
   }
   
   /**
    * Returns the signature parameters of the method.
    * @param method The method.
    * @return The signature parameters.
    */
   protected String getSignatureParameters(ProgramMethod method) {
      StringBuffer sb = new StringBuffer();
      ImmutableArray<ParameterDeclaration> parameters = method.getParameters();
      boolean firstParameter = true;
      for (ParameterDeclaration parameter : parameters) {
         // Check if the parameter is visible in the source code.
         // E.g. inner class constructors have an invisible parameter _ENCLOSING_THIS
         // with the parent class as type, like: _ENCLOSING_THIS : ClassContainer
         Position position = parameter.getStartPosition();
         if (position != null && position.getColumn() > 0 && position.getLine() > 0) {
            if (firstParameter) {
               firstParameter = false;
            }
            else {
               sb.append(PARAMETER_SEPARATOR);
            }
            sb.append(parameter.getVariableSpecification().getFullName());
            sb.append(VAR_NAME_TYPE_SEPARATOR);
            sb.append(getTypeName(parameter.getTypeReference(), DSPackageManagement.NO_PACKAGES));
         }
      }
      return sb.toString();
   }
   
   /**
    * Returns the name of type based on the {@link DSPackageManagement}.
    * @param type The type in KeY.
    * @param packageManagement The {@link DSPackageManagement} to use.
    * @return The type name to use in the diagram model.
    */
   protected String getTypeName(Type type, DSPackageManagement packageManagement) {
      Assert.isTrue(type instanceof KeYJavaType);
      return getTypeName((KeYJavaType)type, packageManagement);
   }
   
   /**
    * Returns the name of type based on the {@link DSPackageManagement}.
    * @param typeReference The type in KeY.
    * @param packageManagement The {@link DSPackageManagement} to use.
    * @return The type name to use in the diagram model.
    */
   protected String getTypeName(TypeReference typeReference, DSPackageManagement packageManagement) {
      return getTypeName(typeReference.getKeYJavaType(), packageManagement);
   }

   /**
    * Returns the name of type based on the {@link DSPackageManagement}.
    * @param type The type in KeY.
    * @param packageManagement The {@link DSPackageManagement} to use.
    * @return The type name to use in the diagram model.
    */
   protected String getTypeName(KeYJavaType type, 
                                DSPackageManagement packageManagement) {
      if (type.getJavaType() instanceof ArrayDeclaration) {
         ArrayDeclaration ad = (ArrayDeclaration)type.getJavaType();
         StringBuffer sb = new StringBuffer();
         sb.append(getTypeName(ad.getBaseType(), packageManagement));
         sb.append(ARRAY_DECLARATION);
         return sb.toString();
      }
      else {
         if (DSPackageManagement.NO_PACKAGES.equals(packageManagement)) {
            return type.getFullName();
         }
         else {
            return type.getName();
         }
      }
   }

   /**
    * Creates a new {@link IDSPackage} instance for the given KeY instance.
    * @param pr The KeY instance.
    * @param packageName The package name to use.
    * @param parent The parent of the new package.
    * @return The created {@link IDSPackage}.
    */
   protected IDSPackage createPackage(PackageReference pr, String packageName, IDSContainer parent) {
      MemoryPackage result = new MemoryPackage(packageName);
      result.setParent(parent);
      return result;
   }
   
   /**
    * Creates a new {@link IDSClass} instance for the given KeY instance.
    * @param services The {@link Services} that is used to read containments.
    * @param ct The KeY class type.
    * @param type The KeY instance.
    * @param interfaceName The class name to use.
    * @return The created {@link IDSClass}.
    * @throws DSException Occurred Exception
    */
   protected MemoryInterface createInterface(Services services, ClassType ct, KeYJavaType type, String interfaceName) throws DSException {
      Assert.isTrue(ct.isInterface());
      MemoryInterface result = new KeyInterface(this, type);
      result.setName(interfaceName);
      // Add methods
      ImmutableList<ProgramMethod> methods = services.getJavaInfo().getAllProgramMethodsLocallyDeclared(type);
      fillInterfaceWithMethods(services, result, methods, type);
      // Add attributes
      result.setStatic(ct.isStatic());
      if (ct.isPrivate()) {
         result.setVisibility(DSVisibility.PRIVATE);
      }
      else if (ct.isProtected()) {
         result.setVisibility(DSVisibility.PROTECTED);
      }
      else if (ct.isPublic()) {
         result.setVisibility(DSVisibility.PUBLIC);
      }
      else {
         result.setVisibility(DSVisibility.DEFAULT);
      }      
      ImmutableList<Field> fields = ct.getAllFields(services);
      for (Field field : fields) {
         ImmutableList<ProgramVariable> vars = services.getJavaInfo().getAllAttributes(field.getFullName(), type);
         for (ProgramVariable var : vars) {
            if (!var.isImplicit()) {
               IDSAttribute attribute = createAttribute(field);
               result.getAttributes().add(attribute);
            }
         }
      }
      // Analyze parents
      ImmutableList<KeYJavaType> superTypes = services.getJavaInfo().getDirectSuperTypes(type);
      for (KeYJavaType superType : superTypes) {
         if (superType.getJavaType() instanceof InterfaceDeclaration) {
            result.getExtendsFullnames().add(superType.getFullName());
         }
         else {
            throw new DSException("Not supported super type: " + superType);
         }
      }
      // Add type invariants
      ImmutableSet<ClassInvariant> classInvariants = services.getSpecificationRepository().getClassInvariants(type);
      for (ClassInvariant classInvariant : classInvariants) {
         MemoryInvariant invariant = createInvariant(services, classInvariant);
         result.addInvariant(invariant);
      }
      typesMapping.put(type, result);
      return result;
   }
   
   /**
    * Creates a new {@link IDSClass} instance for the given KeY instance.
    * @param services The {@link Services} that is used to read containments.
    * @param ct The KeY class type.
    * @param type The KeY instance.
    * @param className The class name to use.
    * @return The created {@link IDSClass}.
    * @throws DSException Occurred Exception
    */
   protected MemoryClass createClass(Services services, ClassType ct, KeYJavaType type, String className) throws DSException {
      Assert.isTrue(!ct.isInterface());
      MemoryClass result = new KeyClass(this, type);
      result.setName(className);
      // Add methods (must be done before constructor adding to collect implicit defined constructors)
      ImmutableList<ProgramMethod> methods = services.getJavaInfo().getAllProgramMethodsLocallyDeclared(type);
      List<ProgramMethod> implicitConstructors = new LinkedList<ProgramMethod>(); 
      fillClassWithMethodsAndConstructors(services, result, methods, implicitConstructors, type);
      // Add constructors with use of implicit constructor definitions to get the specifications
      ImmutableList<ProgramMethod> constructors = services.getJavaInfo().getConstructors(type);
      fillClassWithMethodsAndConstructors(services, result, constructors, implicitConstructors, type);
      // Add attributes
      result.setAnonymous(isAnonymous(ct));
      result.setAbstract(ct.isAbstract());
      result.setFinal(ct.isFinal());
      result.setStatic(ct.isStatic());
      if (ct.isPrivate()) {
         result.setVisibility(DSVisibility.PRIVATE);
      }
      else if (ct.isProtected()) {
         result.setVisibility(DSVisibility.PROTECTED);
      }
      else if (ct.isPublic()) {
         result.setVisibility(DSVisibility.PUBLIC);
      }
      else {
         result.setVisibility(DSVisibility.DEFAULT);
      }      
      ImmutableList<Field> fields = ct.getAllFields(services);
      for (Field field : fields) {
         ImmutableList<ProgramVariable> vars = services.getJavaInfo().getAllAttributes(field.getFullName(), type);
         for (ProgramVariable var : vars) {
            if (!var.isImplicit()) {
               IDSAttribute attribute = createAttribute(field);
               result.getAttributes().add(attribute);
            }
         }
      }
      // Analyze parents
      ImmutableList<KeYJavaType> superTypes = services.getJavaInfo().getDirectSuperTypes(type);
      for (KeYJavaType superType : superTypes) {
         if (superType.getJavaType() instanceof ClassType) {
            ClassType superCt = (ClassType)superType.getJavaType();
            if (superCt.isInterface()) {
               result.getImplementsFullnames().add(superType.getFullName());
            }
            else {
               result.getExtendsFullnames().add(superType.getFullName());
            }
         }
         else if (superType.getJavaType() instanceof InterfaceDeclaration) {
            result.getImplementsFullnames().add(superType.getFullName());
         }
         else {
            throw new DSException("Not supported super type: " + superType);
         }
      }
      ImmutableSet<ClassInvariant> classInvariants = services.getSpecificationRepository().getClassInvariants(type);
      for (ClassInvariant classInvariant : classInvariants) {
         MemoryInvariant invariant = createInvariant(services, classInvariant);
         result.addInvariant(invariant);
      }
      // Add allowed proof obligations
      List<String> classObligations = Collections.emptyList();
      fillProovableWithAllowedOperationContracts(result, classObligations);
      typesMapping.put(type, result);
      return result;
   }

   /**
    * Fills the {@link IDSProvable} with the possible obligations.
    * @param toFill The {@link IDSProvable} to fill.
    * @param obligations The possible obligations.
    * @throws DSException Occurred Exception.
    */
   protected void fillProovableWithAllowedOperationContracts(IDSProvable toFill, List<String> obligations) throws DSException {
      toFill.getObligations().addAll(obligations);
   }

   /**
    * Checks if the class is anonymous or not.
    * @param ct The {@link ClassType} to check.
    * @return {@code true} is anonymous, {@code false} is not anonymous.
    */
   protected boolean isAnonymous(ClassType ct) {
      Assert.isTrue(ct instanceof ClassDeclaration);
      return ((ClassDeclaration)ct).isAnonymousClass();
   }
   
   /**
    * Creates a new {@link IDSOperationContract} instance for the given KeY instance.
    * @param services The services to use.
    * @param operationContract The KeY instance.
    * @param obligations The possible proof obligations
    * @param kjt The {@link KeYJavaType}
    * @param parent The parent.
    * @return The created {@link IDSOperationContract}.
    * @throws DSException Occurred exception
    */   
   protected IDSOperationContract createOperationContract(Services services, 
                                                          ProgramMethod pm,
                                                          FunctionalOperationContract operationContract,
                                                          List<String> obligations,
                                                          KeYJavaType kjt,
                                                          IDSOperation parent) throws DSException {
      KeyOperationContract result = new KeyOperationContract(this,
                                                             kjt,
                                                             pm,
                                                             operationContract);
      result.setParent(parent);
      result.setName(operationContract.getName());
      result.setPre(KeyHacks.getOperationContractPre(services, operationContract));
      result.setPost(KeyHacks.getOperationContractPost(services, operationContract));
      result.setModifies(KeyHacks.getOperationContractModifies(services, operationContract));
      result.setTermination(ObjectUtil.toString(operationContract.getModality()));
      fillProovableWithAllowedOperationContracts(result, obligations);
      operationContractsMapping.put(operationContract, result);
      return result;
   }

   /**
    * Creates a new {@link IDSInvariant} instance for the given KeY instance.
    * @param services The services to use.
    * @param classInvariant The KeY instance.
    * @return The created {@link IDSInvariant}.
    * @throws DSException Occurred exception
    */
   protected MemoryInvariant createInvariant(Services services, 
                                             ClassInvariant classInvariant) throws DSException {
      MemoryInvariant result = new MemoryInvariant();
      result.setName(classInvariant.getName());
      result.setText(KeyHacks.getClassInvariantText(services, classInvariant));
      invariantsMapping.put(classInvariant, result);
      return result;
   }

   /**
    * Creates a new {@link IDSAttribute} instance for the given KeY instance.
    * @param variable The KeY instance.
    * @return The created {@link IDSAttribute}.
    */
   protected IDSAttribute createAttribute(Field variable) {
      MemoryAttribute result = new MemoryAttribute();
      result.setFinal(variable.isFinal());
      result.setName(variable.getProgramName());
      result.setStatic(variable.isStatic());
      result.setType(getTypeName(variable.getType(), DSPackageManagement.NO_PACKAGES));
      if (variable.isPrivate()) {
         result.setVisibility(DSVisibility.PRIVATE);
      }
      else if (variable.isProtected()) {
         result.setVisibility(DSVisibility.PROTECTED);
      }
      else if (variable.isPublic()) {
         result.setVisibility(DSVisibility.PUBLIC);
      }
      else {
         result.setVisibility(DSVisibility.DEFAULT);
      }
      return result;
   }

   /**
    * Creates a new {@link IDSConstructor} instance for the given KeY instance.
    * @param services The services to use.
    * @param explicitConstructor The explicit constructor KeY definition with the correct name.
    * @param implicitConstructor The implicit constructor KeY definition with the specifications.
    * @param type The {@link KeYJavaType}.
    * @param parent The parent of the new constructor.
    * @return The created {@link IDSConstructor}.
    * @throws DSException Occurred Exception
    */
   protected IDSConstructor createConstructor(Services services, 
                                              ProgramMethod explicitConstructor,
                                              ProgramMethod implicitConstructor, 
                                              KeYJavaType type,
                                              IDSType parent) throws DSException {
      MemoryConstructor result = new KeyConstructor(this, type, implicitConstructor);
      result.setParent(parent);
      result.setSignature(getSignature(explicitConstructor));
      result.setStatic(explicitConstructor.isStatic());
      if (explicitConstructor.isPrivate()) {
         result.setVisibility(DSVisibility.PRIVATE);
      }
      else if (explicitConstructor.isProtected()) {
         result.setVisibility(DSVisibility.PROTECTED);
      }
      else if (explicitConstructor.isPublic()) {
         result.setVisibility(DSVisibility.PUBLIC);
      }
      else {
         result.setVisibility(DSVisibility.DEFAULT);
      }
      // Add operation contracts and obligations
      fillOperationContractsAndObligations(result, services, type, implicitConstructor);
      // Update internal mappings
      operationsMapping.put(explicitConstructor, result);
      operationsMapping.put(implicitConstructor, result);
      return result;
   }
   
   /**
    * Fills the {@link IDSOperation} with operation contracts and possible obligations.
    * @param toFill The {@link IDSOperation} to fill.
    * @param services The {@link Services} to use.
    * @param type The java type.
    * @param pm The method/constructor
    * @throws DSException Occurred Exception
    */
   protected void fillOperationContractsAndObligations(IDSOperation toFill, 
                                                       Services services, 
                                                       KeYJavaType type, 
                                                       ProgramMethod pm) throws DSException {
      // Get all possible proofs
      ImmutableSet<FunctionalOperationContract> operationContracts = services.getSpecificationRepository().getOperationContracts(type, pm);
      // Separate between proofs for contracts and for operation itself
      List<String> contractObligations = new LinkedList<String>();
      contractObligations.add(PROOF_OBLIGATION_OPERATION_CONTRACT);
      List<String> methodObligations = new LinkedList<String>();
      fillProovableWithAllowedOperationContracts(toFill, methodObligations);
      // Add operation contracts
      for (FunctionalOperationContract operationContract : operationContracts) {
         IDSOperationContract contract = createOperationContract(services, pm, operationContract, contractObligations, type, toFill);
         toFill.getOperationContracts().add(contract);
      }
   }

   /**
    * Creates a new {@link IDSConstructor} instance for the given KeY instance.
    * @param services The services to use
    * @param method The KeY instance.
    * @param kjt The {@link KeYJavaType}.
    * @param parent The parent of this method.
    * @return The created {@link IDSMethod}.
    * @throws DSException Occurred Exception
    */
   protected IDSMethod createMethod(Services services, ProgramMethod method, KeYJavaType kjt, IDSType parent) throws DSException {
      MemoryMethod result = new KeyMethod(this, kjt, method);
      result.setParent(parent);
      result.setSignature(getSignature(method));
      result.setAbstract(method.isAbstract());
      result.setFinal(method.isFinal());
      result.setStatic(method.isStatic());
      if (method.isPrivate()) {
         result.setVisibility(DSVisibility.PRIVATE);
      }
      else if (method.isProtected()) {
         result.setVisibility(DSVisibility.PROTECTED);
      }
      else if (method.isPublic()) {
         result.setVisibility(DSVisibility.PUBLIC);
      }
      else {
         result.setVisibility(DSVisibility.DEFAULT);
      }
      if (method.getMethodDeclaration() != null && method.getMethodDeclaration().getTypeReference() != null) {
         String returnType = getTypeName(method.getMethodDeclaration().getTypeReference(), DSPackageManagement.NO_PACKAGES);
         result.setReturnType(returnType);
      }
      else {
         result.setReturnType(VOID);
      }
      // Add operation contracts and obligations
      fillOperationContractsAndObligations(result, services, kjt, method);
      // Update internal mappings
      operationsMapping.put(method, result);
      return result;
   }

   /**
    * Fills the interface with methods from the given KeY instances.
    * @param services The services to use.
    * @param toFill The class to fill.
    * @param methodsAndConstructors The available KeY instances.
    * @throws DSException Occurred Exception
    */
   protected void fillInterfaceWithMethods(Services services,
                                           IDSInterface toFill, 
                                           ImmutableList<ProgramMethod> methodsAndConstructors,
                                           KeYJavaType type) throws DSException {
      for (ProgramMethod methodOrConstructor : methodsAndConstructors) {
         if (!methodOrConstructor.isImplicit()) {
            Assert.isTrue(!methodOrConstructor.isConstructor());
            IDSMethod dsMethod = createMethod(services, methodOrConstructor, type, toFill);
            toFill.getMethods().add(dsMethod);
         }
      }
   }
   
   /**
    * Fills the class with constructors and methods from the given KeY instances.
    * @param services The services to use.
    * @param toFill The class to fill.
    * @param methodsAndConstructors The available KeY instances.
    * @param implicitConstructors The implicit constructor definitions to fill and to read from.
    * @throws DSException Occurred Exception
    */
   protected void fillClassWithMethodsAndConstructors(Services services,
                                                      IDSClass toFill, 
                                                      ImmutableList<ProgramMethod> methodsAndConstructors,
                                                      List<ProgramMethod> implicitConstructors,
                                                      KeYJavaType type) throws DSException {
      for (ProgramMethod methodOrConstructor : methodsAndConstructors) {
         if (!methodOrConstructor.isImplicit()) {
            if (methodOrConstructor.isConstructor()) {
               ProgramMethod implicitConstructor = getImplicitConstructor(implicitConstructors, methodOrConstructor);
               Assert.isNotNull(implicitConstructor, "Can't find implicit constructor for: " + methodOrConstructor.getFullName());
               IDSConstructor constructor = createConstructor(services, methodOrConstructor, implicitConstructor, type, toFill);
               toFill.getConstructors().add(constructor);
            }
            else {
               IDSMethod dsMethod = createMethod(services, methodOrConstructor, type, toFill);
               toFill.getMethods().add(dsMethod);
            }
         }
         else {
            if (INIT_NAME.equals(methodOrConstructor.getName())) {
               implicitConstructors.add(methodOrConstructor);
            }
         }
      }
   }

   /**
    * Searches the implicit constructor definition in the given {@link List}
    * for the given explicit constructor definition.
    * @param toSearchIn The available implicit constructor definitions.
    * @param toSearch The explicit constructor definition to search.
    * @return The found implicit constructor or {@code null} if it is not available.
    */
   protected ProgramMethod getImplicitConstructor(List<ProgramMethod> toSearchIn, 
                                                  ProgramMethod toSearch) {
      ProgramMethod result = null;
      Iterator<ProgramMethod> iter = toSearchIn.iterator();
      while (result == null && iter.hasNext()) {
         ProgramMethod next = iter.next();
         // Make sure that the method/constructor is in the same container (e.g. class)
         if (ObjectUtil.equals(toSearch.getContainerType(), next.getContainerType())) {
            // Make sure that the next entry is an implicit constructor
            if (INIT_NAME.equals(next.getName())) {
               // Compare the signature parameters
               String signature1 = getSignatureParameters(toSearch);
               String signature2 = getSignatureParameters(next);
               if (ObjectUtil.equals(signature1, signature2)) {
                  result = next;
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Returns the skip library setting from the settings.
    * @param settings The settings.
    * @return The skip library setting, default is {@code true}.
    */
   protected boolean isSkipLibraryClasses(Map<String, Object> settings) {
      Assert.isNotNull(settings);
      Object object = settings.get(KeyDriver.SETTING_SKIP_LIBRARY_CLASSES);
      if (object != null) {
         Assert.isTrue(object instanceof Boolean);
         return ((Boolean)object).booleanValue();
      }
      else {
         return true;
      }
   }

   /**
    * Returns the location from the settings. Supported locations types are:
    * <ul>
    *    <li>{@link File}</li>
    *    <li>{@link IPath}</li>
    *    <li>{@link IResource}</li>
    * </ul>
    * @param settings The settings.
    * @return The location.
    * @throws DSException Occurred Exception.
    */
   protected File getLocation(Map<String, Object> settings) throws DSException {
      Assert.isNotNull(settings);
      Object object = settings.get(KeyDriver.SETTING_LOCATION);
      if (object instanceof File) {
         return (File)object;
      }
      else if (object instanceof IPath) {
         IResource resource = ResourcesPlugin.getWorkspace().getRoot().findMember((IPath)object);
         if (resource == null) {
            throw new DSException("The resource \"" + object + "\" no longer exists in the workspace.");
         }
         return ResourceUtil.getLocation(resource);
      }
      else {
         throw new DSException("Not supported location: " + object);
      }
   }

   /**
    * Returns the boot class path configured in the {@link IProject}
    * that contains the target location.
    * @param settings The connection settings.
    * @return The found boot class path or {@code null} if no one is available.
    * @throws CoreException Occurred Exception.
    */
   protected File getBootClassPath(Map<String, Object> settings) throws CoreException {
      Assert.isNotNull(settings);
      Object object = settings.get(KeyDriver.SETTING_LOCATION);
      if (object instanceof IPath) {
         IResource resource = ResourcesPlugin.getWorkspace().getRoot().findMember((IPath)object);
         if (resource != null) {
            return KeYResourceProperties.getKeYBootClassPathLocation(resource.getProject());
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
    * Returns the class path entries configured in the {@link IProject}
    * that contains the target location.
    * @param settings The connection settings.
    * @return The found class path entries or {@code null} if no one are available.
    * @throws CoreException Occurred Exception.
    */
   protected List<File> getClassPathEntries(Map<String, Object> settings) throws CoreException {
      Assert.isNotNull(settings);
      Object object = settings.get(KeyDriver.SETTING_LOCATION);
      if (object instanceof IPath) {
         IResource resource = ResourcesPlugin.getWorkspace().getRoot().findMember((IPath)object);
         if (resource != null) {
            return KeYResourceProperties.getKeYClassPathEntries(resource.getProject());
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
    * Returns the package management from the settings.
    * @param settings The settings.
    * @return The {@link DSPackageManagement}.
    */
   protected DSPackageManagement getPackageManagent(Map<String, Object> settings) {
      Assert.isNotNull(settings);
      Object object = settings.get(KeyDriver.SETTING_PACKAGE_MANAGEMENT);
      if (object == null) {
         return DSPackageManagement.getDefault();
      }
      else {
         Assert.isTrue(object instanceof DSPackageManagement);
         return (DSPackageManagement)object;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isConnected() {
      return super.isConnected() && initConfig != null;
   }


   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnect() throws DSException {
      disconnect(true);
   }
   
   /**
    * Executes the disconnect and may closes the opened {@link MainWindow}.
    * @param closeKeYMain Close main window?
    * @throws DSException Occurred Exception.
    */
   protected void disconnect(final boolean closeKeYMain) throws DSException {
      if (main != null) {
         main.getMediator().removeGUIListener(mainGuiListener);
         try {
            final MainWindow oldMain = main;
            final InitConfig oldInitConfig = initConfig;
            Runnable run = new Runnable() {
               @Override
               public void run() {
                  if (oldInitConfig != null) {
                     KeYUtil.removeFromProofList(oldMain, oldInitConfig.getProofEnv());
                  }
                  if (closeKeYMain && KeYUtil.isProofListEmpty(oldMain) && oldMain.getExitMainAction() != null) {
                     oldMain.getExitMainAction().exitMainWithoutInteraction();
                  }
               }
            };
            if (SwingUtil.isSwingThread()) {
               run.run();
            }
            else {
               SwingUtil.invokeLater(run);
            }
         }
         catch (Exception e) {
            throw new DSException(e);
         }
      }
      main = null;
      init = null;
      initConfig = null;
      operationsMapping = null;
      operationContractsMapping = null;
      invariantsMapping = null;
      typesMapping = null;
      super.disconnect();
   }
   
   /**
    * Returns the {@link IDSOperation} instance for the given {@link ProgramMethod} from KeY.
    * @param pm The given {@link ProgramMethod}.
    * @return The mapped {@link IDSOperation} or {@code null} if no data source instance exists.
    */
   public IDSOperation getOperation(ProgramMethod pm) {
      return operationsMapping.get(pm);
   }

   /**
    * Returns the {@link IDSOperationContract} for the give {@link Contract} from KeY.
    * @param oc The given {@link Contract}.
    * @return The mapped {@link IDSOperationContract} or {@code null} if no data source instance exists.
    */
   public IDSOperationContract getOperationContract(Contract oc) {
      return operationContractsMapping.get(oc);
   }

   /**
    * Returns the {@link IDSInvariant} for the give {@link ClassInvariant} from KeY.
    * @param invariant The given {@link ClassInvariant}.
    * @return The mapped {@link IDSInvariant} or {@code null} if no data source instance exists.
    */   
   public IDSInvariant getInvariant(ClassInvariant invariant) {
      return invariantsMapping.get(invariant);
   }
   
   /**
    * Returns the {@link IDSType} for the give {@link KeYJavaType} from KeY.
    * @param type The given {@link KeYJavaType}.
    * @return The mapped {@link IDSType} or {@code null} if no data source instance exists.
    */
   public IDSType getType(KeYJavaType type) {
      return typesMapping.get(type);
   }







   /**
    * Opens the proof.
    * @param type The {@link KeYJavaType} to use or {@code null} if not required.
    * @param pm The {@link ProgramMethod} to use or {@code null} if not required.
    * @param oc The {@link OperationContract} to use or {@code null} if not required.
    * @param obligation The obligation to proof.
    * @return The opened {@link OpenedProof} or {@code null} if no one was opened.
    * @throws DSException Occurred Exception
    * @throws DSCanceledException Occurred Exception
    */
   public OpenedProof openProof(KeYJavaType type,
                                ProgramMethod pm,
                                OperationContract oc,
                                String obligation) throws DSException, DSCanceledException {
      OpenedProof proofResult = createProofInput(type, pm, oc, obligation);
      if (proofResult == null || proofResult.getInput() == null) {
         throw new DSCanceledException();
      }
      Proof proof = openProof(proofResult.getInput());
      proofResult.setProof(proof);
      return proofResult;
   }

   /**
    * <p>
    * Creates the input parameters that are used to open a proof.
    * </p>
    * <p>
    * The implementation is equal to createcreatePO(...) in {@link POBrowser},
    * but the controls to define the target are removed.
    * </p>
    * @param type The {@link KeYJavaType} to use or {@code null} if not required.
    * @param pm The {@link ProgramMethod} to use or {@code null} if not required.
    * @param oc The {@link OperationContract} to use or {@code null} if not required.
    * @param poString The obligation to proof.
    * @return The created {@link OpenedProof} that contains for example the {@link ProofOblInput}.
    * @throws DSException Occurred Exception
    */
   public OpenedProof createProofInput(KeYJavaType type,
                                       ProgramMethod pm,
                                       OperationContract oc,
                                       String poString) throws DSException {
      ProofOblInput input = oc.createProofObl(initConfig, oc);
      return new OpenedProof(input);
   }

   
   /**
    * <p>
    * Opens the proof.
    * </p>
    * <p>
    * Code was copied and modified from {@link Main#showPOBrowser()}
    * </p>
    * @param po The proof to open
    * @return The opened {@link Proof} or {@code null} if no one was opened.
    */
   public Proof openProof(ProofOblInput po) {
      try {
         if (po != null) {
            Proof proof = init.startProver(initConfig, po);
            return proof;
         }
         else {
            return null;
         }
      }
      catch (ProofInputException e) {
         ExceptionDialog.showDialog(MainWindow.getInstance(), e);
         return null;
      }
   }
   
   /**
    * Selects the proof in the user interface.
    * @param proof The proof to select.
    */
   public void selectProof(Proof proof) {
      Assert.isNotNull(proof);
      main.getMediator().setProof(proof);
   }   
   
   /**
    * Checks if the {@link Proof} exists in the user interface.
    * @param proof The {@link Proof} to check.
    * @return {@code true} = in UI, {@code false} = not in UI.
    */
   public boolean isProofInUI(Proof proof) {
      boolean inUI = false;
      if (proof != null) {
         Set<ProofAggregate> proofAggregates = initConfig.getProofEnv().getProofs();
         Iterator<ProofAggregate> iter = proofAggregates.iterator();
         while (!inUI && iter.hasNext()) {
            ProofAggregate next = iter.next();
            inUI = ArrayUtil.contains(next.getProofs(), proof);
         }
      }
      return inUI;
   }

   public Services getServices() {
      return main != null ? main.getMediator().getServices() : null;
   }

   public void closeTaskWithoutInteraction() {
      main.closeTaskWithoutInteraction();
   }
}
