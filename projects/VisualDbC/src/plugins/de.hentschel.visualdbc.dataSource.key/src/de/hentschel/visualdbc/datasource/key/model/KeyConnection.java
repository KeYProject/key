/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.key.model;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.EventObject;
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
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.SwingUtil;

import de.hentschel.visualdbc.datasource.key.intern.helper.KeyHacks;
import de.hentschel.visualdbc.datasource.key.intern.helper.OpenedProof;
import de.hentschel.visualdbc.datasource.key.model.event.IKeYConnectionListener;
import de.hentschel.visualdbc.datasource.key.model.event.KeYConnectionEvent;
import de.hentschel.visualdbc.datasource.key.util.LogUtil;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSContainer;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
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
import de.hentschel.visualdbc.datasource.model.memory.MemoryAxiom;
import de.hentschel.visualdbc.datasource.model.memory.MemoryAxiomContract;
import de.hentschel.visualdbc.datasource.model.memory.MemoryClass;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnection;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConstructor;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnum;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnumLiteral;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInterface;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInvariant;
import de.hentschel.visualdbc.datasource.model.memory.MemoryMethod;
import de.hentschel.visualdbc.datasource.model.memory.MemoryPackage;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.UserInterface;

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
    * The used {@link KeYEnvironment}.
    */
   private KeYEnvironment<?> environment;
   
   /**
    * Maps all {@link IProgramMethod}s to their data source instance.
    */
   private Map<IProgramMethod, IDSOperation> operationsMapping;

   /**
    * Maps all {@link OperationContract}s to their data source instance.
    */
   private Map<OperationContract, IDSOperationContract> operationContractsMapping;

   /**
    * Maps all {@link OperationContract}s to their data source instance.
    */
   private Map<Contract, IDSAxiomContract> axiomContractsMapping;
   
   /**
    * Maps all {@link ClassInvariant}s to their data source instance.
    */
   private Map<ClassInvariant, IDSInvariant> invariantsMapping;
   
   /**
    * Maps all {@link ClassAxiom}s to their data source instance.
    */
   private Map<ClassAxiom, IDSAxiom> axiomsMapping;
   
   /**
    * Maps all {@link IProgramVariable}s to their data source instance.
    */
   private Map<IProgramVariable, IDSAttribute> attributesMapping;
   
   /**
    * Maps all {@link IProgramVariable}s to their data source instance.
    */
   private Map<IProgramVariable, IDSEnumLiteral> enumLiteralsMapping;
   
   /**
    * Maps all {@link KeYJavaType}s to their data source instance.
    */
   private Map<KeYJavaType, IDSType> typesMapping;
   
   /**
    * Contains all instantiated {@link KeyProof}s to dispose them on disconnect.
    */
   private List<KeyProof> proofs;
   
   /**
    * Contains the registered {@link IKeYConnectionListener}.
    */
   private List<IKeYConnectionListener> listeners = new LinkedList<IKeYConnectionListener>();
   
   /**
    * The used listener to observe {@link #main}.
    */
   private GUIListener mainGuiListener = new GUIListener() {
      @Override
      public void shutDown(EventObject e) {
         handleMainClosed(e);
      }
      
      @Override
      public void modalDialogOpened(EventObject e) {
      }
      
      @Override
      public void modalDialogClosed(EventObject e) {
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
         operationsMapping = new HashMap<IProgramMethod, IDSOperation>();
         operationContractsMapping = new HashMap<OperationContract, IDSOperationContract>();
         axiomContractsMapping = new HashMap<Contract, IDSAxiomContract>();
         invariantsMapping = new HashMap<ClassInvariant, IDSInvariant>();
         typesMapping = new HashMap<KeYJavaType, IDSType>();
         axiomsMapping = new HashMap<ClassAxiom, IDSAxiom>();
         attributesMapping = new HashMap<IProgramVariable, IDSAttribute>();
         enumLiteralsMapping = new HashMap<IProgramVariable, IDSEnumLiteral>();
         proofs = new LinkedList<KeyProof>();
         // Get settings
         final File location = getLocation(connectionSettings);
         final List<File> classPathEntries = getClassPathEntries(connectionSettings);
         final File bootClassPath = getBootClassPath(connectionSettings);
         if (location == null || !location.exists()) {
            throw new DSException("The location \"" + location + "\" doesn't exist.");
         }
         final boolean skipLibraryClasses = isSkipLibraryClasses(connectionSettings);
         final DSPackageManagement packageManagement = getPackageManagent(connectionSettings);
         
         // Establish connection
         if (interactive) {
            environment = KeYEnvironment.loadInMainWindow(location, classPathEntries, bootClassPath, true);
            KeYMediator mediator = environment.getMediator();
            mediator.addGUIListener(mainGuiListener);
         }
         else {
            environment = KeYEnvironment.load(location, classPathEntries, bootClassPath);
         }
         initConfig = environment.getInitConfig();
         // Analyze classes, interfaces, enums and packages
         analyzeTypes(environment.getServices(), skipLibraryClasses, packageManagement, monitor);
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
   protected void handleMainClosed(EventObject e) {
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
      Map<String, List<MemoryEnum>> innerEnums = new HashMap<String, List<MemoryEnum>>(); // Contains all inner classes that are added to their parents after analyzing all types to make sure that the parent type already exists as IDSType.
      Map<String, IDSType> types = new HashMap<String, IDSType>(); // Maps the full name to the created IDSType.
      monitor.beginTask("Analyzing types", kjtsarr.length);
      for (KeYJavaType type : kjtsarr) {
         // Create class
         String typeName = getTypeName(type, packageManagement);
         Assert.isTrue(type.getJavaType() instanceof ClassType);
         ClassType ct = (ClassType)type.getJavaType();
         if (KeYTypeUtil.isInnerType(services, type)) {
            String parentName = KeYTypeUtil.getParentName(services, type);
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
            else if (ct instanceof EnumClassDeclaration) {
               MemoryEnum enumInstance = createEnum(services, (EnumClassDeclaration)ct, type, typeName);
               List<MemoryEnum> parentInnerEnums = innerEnums.get(parentName);
               if (parentInnerEnums == null) {
                  parentInnerEnums = new LinkedList<MemoryEnum>();
                  innerEnums.put(parentName, parentInnerEnums);
               }
               parentInnerEnums.add(enumInstance);
               types.put(type.getFullName(), enumInstance);
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
               else if (ct instanceof EnumClassDeclaration) {
                  MemoryEnum enumInstance = createEnum(services, (EnumClassDeclaration)ct, type, typeName);
                  enumInstance.setParentContainer(dsPackage);
                  dsPackage.getEnums().add(enumInstance);
                  types.put(type.getFullName(), enumInstance);
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
               else if (ct instanceof EnumClassDeclaration) {
                  MemoryEnum enumInstance = createEnum(services, (EnumClassDeclaration)ct, type, typeName);
                  enumInstance.setParentContainer(this);
                  getEnums().add(enumInstance);
                  types.put(type.getFullName(), enumInstance);
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
      // Add inner enumeration to their parents
      monitor.beginTask("Adding inner enums", innerInterfaces.size());
      Set<Entry<String, List<MemoryEnum>>> innerEnumEntries = innerEnums.entrySet();
      for (Entry<String, List<MemoryEnum>> innerEntry : innerEnumEntries) {
         IDSType parent = types.get(innerEntry.getKey());
         Assert.isNotNull(parent);
         List<MemoryEnum> innerEnumList = innerEntry.getValue();
         Assert.isNotNull(innerEnumList);
         for (MemoryEnum innerEnum : innerEnumList) {
            parent.getInnerEnums().add(innerEnum);
            innerEnum.setParentType(parent);
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
         else if (type instanceof IDSEnum) {
            IDSEnum enumInstance = (IDSEnum)type;
            for (String parent : enumInstance.getImplementsFullnames()) {
               IDSType parentInstance = types.get(parent);
               if (parentInstance != null) {
                  Assert.isTrue(parentInstance instanceof IDSInterface); 
                  enumInstance.getImplements().add((IDSInterface)parentInstance);
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
   public static String getSignature(IProgramMethod method) {
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
   public static String getSignatureParameters(IProgramMethod method) {
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
   public static String getTypeName(Type type, DSPackageManagement packageManagement) {
      Assert.isTrue(type instanceof KeYJavaType);
      return getTypeName((KeYJavaType)type, packageManagement);
   }
   
   /**
    * Returns the name of type based on the {@link DSPackageManagement}.
    * @param typeReference The type in KeY.
    * @param packageManagement The {@link DSPackageManagement} to use.
    * @return The type name to use in the diagram model.
    */
   public static String getTypeName(TypeReference typeReference, DSPackageManagement packageManagement) {
      return getTypeName(typeReference.getKeYJavaType(), packageManagement);
   }

   /**
    * Returns the name of type based on the {@link DSPackageManagement}.
    * @param type The type in KeY.
    * @param packageManagement The {@link DSPackageManagement} to use.
    * @return The type name to use in the diagram model.
    */
   public static String getTypeName(KeYJavaType type, 
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
      Assert.isTrue(!(ct instanceof EnumClassDeclaration));
      MemoryInterface result = new KeyInterface(this, type);
      result.setName(interfaceName);
      // Add methods
      ImmutableList<IProgramMethod> methods = services.getJavaInfo().getAllProgramMethodsLocallyDeclared(type);
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
               MemoryAttribute attribute = createAttribute(services, field);
               attribute.setParent(result);
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
         invariant.setParent(result);
         result.addInvariant(invariant);
      }
      // Add type axioms
      ImmutableSet<ClassAxiom> axioms = services.getSpecificationRepository().getClassAxioms(type);
      for (ClassAxiom classAxiom : axioms) {
         if (shouldIncludeClassAxiom(services, type, classAxiom)) {
            MemoryAxiom axiom = createAxiom(services, type, classAxiom);
            axiom.setParent(result);
            result.addAxiom(axiom);
         }
      }
      typesMapping.put(type, result);
      return result;
   }

   /**
    * Checks if the given {@link ClassAxiom} should be included.
    * @param services The {@link Services} to use.
    * @param type The current {@link KeYJavaType}
    * @param classAxiom The {@link ClassAxiom} to check.
    * @return {@code true} include, {@code false} do not include
    */
   public static boolean shouldIncludeClassAxiom(Services services, KeYJavaType type, ClassAxiom classAxiom) {
      if (classAxiom.getKJT() != type) {
         return false; // Axiom is declared in different class, ignore it.
      }
      else {
         ImmutableSet<IObserverFunction> targets = services.getSpecificationRepository().getContractTargets(type);
         return classAxiom instanceof RepresentsAxiom && // Filter other axiom types out
                ((classAxiom.getTarget() != null && classAxiom.getTarget().getType() != null) || // Allow also represents axioms without accessible clause.
                CollectionUtil.contains(targets, classAxiom.getTarget())); // Make sure that everything that has an accessible clause is available.
      }
   }

   /**
    * Creates a new {@link IDSEnum} instance for the given KeY instance.
    * @param services The {@link Services} that is used to read containments.
    * @param ct The KeY class type.
    * @param type The KeY instance.
    * @param className The class name to use.
    * @return The created {@link IDSClass}.
    * @throws DSException Occurred Exception
    */   
   protected MemoryEnum createEnum(Services services, EnumClassDeclaration ct, KeYJavaType type, String className) throws DSException {
      Assert.isTrue(!ct.isInterface());
      Assert.isTrue(ct instanceof EnumClassDeclaration);
      MemoryEnum result = new KeyEnum(this, type);
      result.setName(className);
      // Add methods (must be done before constructor adding to collect implicit defined constructors)
      ImmutableList<IProgramMethod> methods = services.getJavaInfo().getAllProgramMethodsLocallyDeclared(type);
      List<IProgramMethod> implicitConstructors = new LinkedList<IProgramMethod>(); 
      fillEnumWithMethodsAndConstructors(services, result, methods, implicitConstructors, type);
      // Add constructors with use of implicit constructor definitions to get the specifications
      ImmutableList<IProgramMethod> constructors = services.getJavaInfo().getConstructors(type);
      fillEnumWithMethodsAndConstructors(services, result, constructors, implicitConstructors, type);
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
               if (EnumClassDeclaration.isEnumConstant(field.getProgramVariable())) {
                  // Enumeration literal
                  MemoryEnumLiteral literal = createEnumLiteral(services, field);
                  literal.setParent(result);
                  result.getLiterals().add(literal);
               }
               else {
                  // Attribute
                  MemoryAttribute attribute = createAttribute(services, field);
                  attribute.setParent(result);
                  result.getAttributes().add(attribute);
               }
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
         }
         else if (superType.getJavaType() instanceof InterfaceDeclaration) {
            result.getImplementsFullnames().add(superType.getFullName());
         }
         else {
            throw new DSException("Not supported super type: " + superType);
         }
      }
      // Add type invariants
      ImmutableSet<ClassInvariant> classInvariants = services.getSpecificationRepository().getClassInvariants(type);
      for (ClassInvariant classInvariant : classInvariants) {
         MemoryInvariant invariant = createInvariant(services, classInvariant);
         invariant.setParent(result);
         result.addInvariant(invariant);
      }
      // Add type axioms
      ImmutableSet<ClassAxiom> axioms = services.getSpecificationRepository().getClassAxioms(type);
      for (ClassAxiom classAxiom : axioms) {
         if (shouldIncludeClassAxiom(services, type, classAxiom)) {
            MemoryAxiom axiom = createAxiom(services, type, classAxiom);
            axiom.setParent(result);
            result.addAxiom(axiom);
         }
      }
      // Add allowed proof obligations
      List<String> classObligations = Collections.emptyList();
      fillProovableWithAllowedOperationContracts(result, classObligations);
      typesMapping.put(type, result);
      return result;
   }

   /**
    * Creates a new {@link IDSEnumLiteral} instance for the given KeY instance.
    * @param field The KeY instance.
    * @return The created {@link IDSEnumLiteral}.
    */
   protected MemoryEnumLiteral createEnumLiteral(Services services, Field field) {
      MemoryEnumLiteral result = new MemoryEnumLiteral();
      result.setName(field.getProgramName());
      enumLiteralsMapping.put(field.getProgramVariable(), result);
      return result;
   }
   
   /**
    * Fills the enumeration with constructors and methods from the given KeY instances.
    * @param services The services to use.
    * @param toFill The class to fill.
    * @param methodsAndConstructors The available KeY instances.
    * @param implicitConstructors The implicit constructor definitions to fill and to read from.
    * @throws DSException Occurred Exception
    */
   protected void fillEnumWithMethodsAndConstructors(Services services,
                                                     IDSEnum toFill, 
                                                     ImmutableList<IProgramMethod> methodsAndConstructors,
                                                     List<IProgramMethod> implicitConstructors,
                                                     KeYJavaType type) throws DSException {
      for (IProgramMethod methodOrConstructor : methodsAndConstructors) {
         if (!methodOrConstructor.isImplicit()) {
            if (methodOrConstructor.isConstructor()) {
               IProgramMethod implicitConstructor = getImplicitConstructor(implicitConstructors, methodOrConstructor);
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
      Assert.isTrue(!(ct instanceof EnumClassDeclaration));
      MemoryClass result = new KeyClass(this, type);
      result.setName(className);
      // Add methods (must be done before constructor adding to collect implicit defined constructors)
      ImmutableList<IProgramMethod> methods = services.getJavaInfo().getAllProgramMethodsLocallyDeclared(type);
      List<IProgramMethod> implicitConstructors = new LinkedList<IProgramMethod>(); 
      fillClassWithMethodsAndConstructors(services, result, methods, implicitConstructors, type);
      // Add constructors with use of implicit constructor definitions to get the specifications
      ImmutableList<IProgramMethod> constructors = services.getJavaInfo().getConstructors(type);
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
               MemoryAttribute attribute = createAttribute(services, field);
               attribute.setParent(result);
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
      // Add type invariants
      ImmutableSet<ClassInvariant> classInvariants = services.getSpecificationRepository().getClassInvariants(type);
      for (ClassInvariant classInvariant : classInvariants) {
         MemoryInvariant invariant = createInvariant(services, classInvariant);
         invariant.setParent(result);
         result.addInvariant(invariant);
      }
      // Add type axioms
      ImmutableSet<ClassAxiom> axioms = services.getSpecificationRepository().getClassAxioms(type);
      for (ClassAxiom classAxiom : axioms) {
         if (shouldIncludeClassAxiom(services, type, classAxiom)) {
            MemoryAxiom axiom = createAxiom(services, type, classAxiom);
            axiom.setParent(result);
            result.addAxiom(axiom);
         }
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
                                                          IProgramMethod pm,
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
    * Creates a new {@link IDSAxiom} instance for the given KeY instance.
    * @param services The services to use.
    * @param classAxiom The KeY instance.
    * @return The created {@link IDSAxiom}.
    * @throws DSException Occurred exception
    */
   protected MemoryAxiom createAxiom(Services services, 
                                     KeYJavaType type,
                                     ClassAxiom classAxiom) throws DSException {
      MemoryAxiom result = new MemoryAxiom();
      result.setName(classAxiom.getName());
      result.setDefinition(ObjectUtil.toString(classAxiom));
      fillAxiomContracts(result, services, type, classAxiom);
      axiomsMapping.put(classAxiom, result);
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
   protected void fillAxiomContracts(IDSAxiom toFill, 
                                     Services services, 
                                     KeYJavaType type, 
                                     ClassAxiom classAxiom) throws DSException {
      // Get all possible contracts
      ImmutableSet<Contract> contracts = services.getSpecificationRepository().getAllContracts();
      // Separate between proofs for contracts and for operation itself
      List<String> contractObligations = new LinkedList<String>();
      contractObligations.add(PROOF_OBLIGATION_OPERATION_CONTRACT);
      List<String> methodObligations = new LinkedList<String>();
      fillProovableWithAllowedOperationContracts(toFill, methodObligations);
      // Add operation contracts
      for (Contract contract : contracts) {
         if (contract instanceof DependencyContract &&
             ObjectUtil.equals(classAxiom.getTarget(), contract.getTarget())) {
            MemoryAxiomContract axiomContract = createAxiomContract(services, (DependencyContract)contract, contractObligations, type, toFill);
            toFill.getAxiomContracts().add(axiomContract);
         }
      }
   }
   
   /**
    * Creates a new {@link IDSAxiomContract} instance for the given KeY instance.
    * @param services The services to use.
    * @param contract The KeY instance.
    * @param obligations The possible proof obligations
    * @param kjt The {@link KeYJavaType}
    * @param parent The parent.
    * @return The created {@link IDSAxiomContract}.
    * @throws DSException Occurred exception
    */   
   protected MemoryAxiomContract createAxiomContract(Services services, 
                                                     DependencyContract contract,
                                                     List<String> obligations,
                                                     KeYJavaType kjt,
                                                     IDSAxiom parent) throws DSException {
      MemoryAxiomContract result = new KeyAxiomContract(this, kjt, contract);
      result.setParent(parent);
      result.setName(contract.getName());
      result.setPre(KeyHacks.getOperationContractPre(services, contract));
      result.setDep(KeyHacks.getDependencyContractDep(services, (DependencyContract)contract));
      fillProovableWithAllowedOperationContracts(result, obligations);
      axiomContractsMapping.put(contract, result);
      return result;
   }

   /**
    * Creates a new {@link IDSAttribute} instance for the given KeY instance.
    * @param field The KeY instance.
    * @return The created {@link IDSAttribute}.
    */
   protected MemoryAttribute createAttribute(Services services, Field field) {
      MemoryAttribute result = new MemoryAttribute();
      result.setFinal(field.isFinal());
      result.setName(field.getProgramName());
      result.setStatic(field.isStatic());
      result.setType(getTypeName(field.getType(), DSPackageManagement.NO_PACKAGES));
      if (field.isPrivate()) {
         result.setVisibility(DSVisibility.PRIVATE);
      }
      else if (field.isProtected()) {
         result.setVisibility(DSVisibility.PROTECTED);
      }
      else if (field.isPublic()) {
         result.setVisibility(DSVisibility.PUBLIC);
      }
      else {
         result.setVisibility(DSVisibility.DEFAULT);
      }
      attributesMapping.put(field.getProgramVariable(), result);
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
                                              IProgramMethod explicitConstructor,
                                              IProgramMethod implicitConstructor, 
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
      fillOperationContractsAndObligations(result, services, type, explicitConstructor);
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
                                                       IProgramMethod pm) throws DSException {
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
   protected IDSMethod createMethod(Services services, IProgramMethod method, KeYJavaType kjt, IDSType parent) throws DSException {
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
                                           ImmutableList<IProgramMethod> methodsAndConstructors,
                                           KeYJavaType type) throws DSException {
      for (IProgramMethod methodOrConstructor : methodsAndConstructors) {
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
                                                      ImmutableList<IProgramMethod> methodsAndConstructors,
                                                      List<IProgramMethod> implicitConstructors,
                                                      KeYJavaType type) throws DSException {
      for (IProgramMethod methodOrConstructor : methodsAndConstructors) {
         if (!methodOrConstructor.isImplicit()) {
            if (methodOrConstructor.isConstructor()) {
               IProgramMethod implicitConstructor = getImplicitConstructor(implicitConstructors, methodOrConstructor);
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
   protected IProgramMethod getImplicitConstructor(List<IProgramMethod> toSearchIn, 
                                                   IProgramMethod toSearch) {
      IProgramMethod result = null;
      Iterator<IProgramMethod> iter = toSearchIn.iterator();
      while (result == null && iter.hasNext()) {
         IProgramMethod next = iter.next();
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
      // Dispose proofs
      for (KeyProof proof : proofs) {
         proof.dispose();
      }
      // Remove listener and proof environment
      if (environment != null) {
         environment.getMediator().removeGUIListener(mainGuiListener);
         try {
            final MainWindow oldMain = MainWindow.getInstance();
            if (oldMain.getUserInterface() == environment.getUi()) {
               Runnable run = new Runnable() {
                  @Override
                  public void run() {
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
         }
         catch (Exception e) {
            throw new DSException(e);
         }
      }
      environment = null;
      initConfig = null;
      operationsMapping = null;
      operationContractsMapping = null;
      axiomContractsMapping = null;
      invariantsMapping = null;
      axiomsMapping = null;
      typesMapping = null;
      attributesMapping = null;
      enumLiteralsMapping = null;
      proofs = null;
      super.disconnect();
   }
   
   /**
    * Returns the {@link IDSOperation} instance for the given {@link IProgramMethod} from KeY.
    * @param pm The given {@link IProgramMethod}.
    * @return The mapped {@link IDSOperation} or {@code null} if no data source instance exists.
    */
   public IDSOperation getOperation(IProgramMethod pm) {
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
    * Returns the {@link IDSAxiomContract} for the give {@link Contract} from KeY.
    * @param ac The given {@link Contract}.
    * @return The mapped {@link IDSAxiomContract} or {@code null} if no data source instance exists.
    */
   public IDSAxiomContract getAxiomContract(Contract ac) {
      return axiomContractsMapping.get(ac);
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
    * Returns the {@link IDSAxiom} for the give {@link ClassAxiom} from KeY.
    * @param axiom The given {@link ClassAxiom}.
    * @return The mapped {@link IDSAxiom} or {@code null} if no data source instance exists.
    */   
   public IDSAxiom getAxiom(ClassAxiom axiom) {
      return axiomsMapping.get(axiom);
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
    * Returns the {@link IDSAttribute} instance for the given {@link IProgramVariable} from KeY.
    * @param variable The given {@link IProgramVariable}.
    * @return The mapped {@link IDSAttribute} or {@code null} if no data source instance exists.
    */
   public IDSAttribute getAttribute(IProgramVariable variable) {
      return attributesMapping.get(variable);
   }
   
   /**
    * Returns the {@link IDSEnumLiteral} instance for the given {@link IProgramVariable} from KeY.
    * @param variable The given {@link IProgramVariable}.
    * @return The mapped {@link IDSEnumLiteral} or {@code null} if no data source instance exists.
    */
   public IDSEnumLiteral getEnumLiteral(IProgramVariable variable) {
      return enumLiteralsMapping.get(variable);
   }







   /**
    * Opens the proof.
    * @param type The {@link KeYJavaType} to use or {@code null} if not required.
    * @param pm The {@link IProgramMethod} to use or {@code null} if not required.
    * @param oc The {@link Contract} to use or {@code null} if not required.
    * @param obligation The obligation to proof.
    * @return The opened {@link OpenedProof} or {@code null} if no one was opened.
    * @throws DSException Occurred Exception
    * @throws DSCanceledException Occurred Exception
    */
   public OpenedProof openProof(KeYJavaType type,
                                IProgramMethod pm,
                                Contract oc,
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
    * @param pm The {@link IProgramMethod} to use or {@code null} if not required.
    * @param oc The {@link Contract} to use or {@code null} if not required.
    * @param poString The obligation to proof.
    * @return The created {@link OpenedProof} that contains for example the {@link ProofOblInput}.
    * @throws DSException Occurred Exception
    */
   public OpenedProof createProofInput(KeYJavaType type,
                                       IProgramMethod pm,
                                       Contract oc,
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
            Proof proof = environment.createProof(po);
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
      environment.getMediator().setProof(proof);
   }

   /**
    * Returns the used {@link Services}.
    * @return The used {@link Services}.
    */
   public Services getServices() {
      return environment != null ? environment.getServices() : null;
   }

   /**
    * Returns the used {@link UserInterface}.
    * @return The used {@link UserInterface}.
    */
   public UserInterface getUserInterface() {
      return environment != null ? environment.getUi() : null;
   }

   /**
    * Closes the active task without user interaction.
    */
   public void closeTaskWithoutInteraction() {
      environment.getUi().removeProof(environment.getMediator().getSelectedProof());
   }
   
   /**
    * Registers the {@link KeyProof} in this {@link KeyConnection}.
    * @param proof The {@link KeyProof} to register.
    */
   public void registerProof(KeyProof proof) {
      Assert.isTrue(proofs != null, "Connection is not established.");
      proofs.add(proof);
   }
   
   /**
    * Registers the given {@link IKeYConnectionListener}.
    * @param l The {@link IKeYConnectionListener} to register.
    */
   public void addKeYConnectionListener(IKeYConnectionListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }
   
   /**
    * Removes the given {@link IKeYConnectionListener}.
    * @param l The {@link IKeYConnectionListener} to remove.
    */
   public void removeKeYConnectionListener(IKeYConnectionListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }
   
   /**
    * Checks if the given {@link IKeYConnectionListener} is registered.
    * @param l The {@link IKeYConnectionListener} to check.
    * @return {@code true} is registered, {@code false} is not registered.
    */
   public boolean hasKeYConnectionListener(IKeYConnectionListener l) {
      return l != null ? listeners.contains(l) : false;
   }
   
   /**
    * Fires the event {@link IKeYConnectionListener#interactiveProofStarted(KeYConnectionEvent)} to all listeners.
    * @param e The event to fire.
    */
   protected void fireInteractiveProofStarted(KeyProof proof) {
      fireInteractiveProofStarted(new KeYConnectionEvent(this, proof));
   }
   
   /**
    * Fires the event {@link IKeYConnectionListener#interactiveProofStarted(KeYConnectionEvent)} to all listeners.
    * @param e The event to fire.
    */
   protected void fireInteractiveProofStarted(KeYConnectionEvent e) {
      IKeYConnectionListener[] toInform = listeners.toArray(new IKeYConnectionListener[listeners.size()]);
      for (IKeYConnectionListener l : toInform) {
         l.interactiveProofStarted(e);
      }
   }
}