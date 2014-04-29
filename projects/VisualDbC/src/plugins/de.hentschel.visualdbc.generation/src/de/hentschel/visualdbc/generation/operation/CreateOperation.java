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

package de.hentschel.visualdbc.generation.operation;

import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.OperationHistoryFactory;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.gmf.runtime.common.core.command.CommandResult;
import org.eclipse.gmf.runtime.diagram.core.services.ViewService;
import org.eclipse.gmf.runtime.emf.commands.core.command.AbstractTransactionalCommand;
import org.eclipse.gmf.runtime.emf.core.GMFEditingDomainFactory;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PartInitException;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcPackage;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorUtil;
import de.hentschel.visualdbc.dbcmodel.diagram.part.Messages;
import de.hentschel.visualdbc.generation.util.LogUtil;

//TODO: Add support for DbcProof
//TODO: Add support for DbcProofReference
//TODO: Use default commands instead of setting values directly!
/**
 * <p>
 * Creates the {@link DbcModel} and the diagram file from the information
 * provided by an {@link IDSConnection}.
 * </p>
 * <p>
 * <b>Attention:</b> This class is not multi threading save.
 * </p>
 * @author Martin Hentschel
 */
public class CreateOperation {
   /**
    * The {@link IDSConnection} to use.
    */
   private IDSConnection connection;
   
   /**
    * The target model file to create.
    */
   private URI modelURI;
   
   /**
    * The target diagram file to create.
    */
   private URI diagramURI;
   
   /**
    * Mapping of the {@link IDSType} to the {@link AbstractDbcType} that is required
    * to set the implements and extends references after the containment hierarchy was created.
    */
   private Map<IDSType, AbstractDbcType> mapping = new HashMap<IDSType, AbstractDbcType>();
   
   /**
    * Constructor.
    * @param connection The {@link IDSConnection} to use.
    * @param modelFile The target model file to create. 
    * @param diagramFile The target diagram file to create.
    */
   public CreateOperation(IDSConnection connection,
                          IFile modelFile,
                          IFile diagramFile) {
      this(connection, 
           URI.createPlatformResourceURI(modelFile.getFullPath().toString(), false), 
           URI.createPlatformResourceURI(diagramFile.getFullPath().toString(), false));
   }
   
   /**
    * Constructor.
    * @param connection The {@link IDSConnection} to use.
    * @param modelURI The target model file to create. 
    * @param diagramURI The target diagram file to create.
    */
   public CreateOperation(IDSConnection connection,
                          URI modelURI,
                          URI diagramURI) {
      Assert.isNotNull(connection);
      Assert.isNotNull(modelURI);
      Assert.isNotNull(diagramURI);
      this.connection = connection;
      this.modelURI = modelURI;
      this.diagramURI = diagramURI;
   }
   
   /**
    * <p>
    * Creates the model and the target diagram.
    * </p>
    * <p>
    * <b>Attention:</b> This method is not multi threading save!
    * </p>
    * @param monitor The {@link IProgressMonitor} to use.
    * @param openCratedDiagram Indicates that the created diagram should be opened in the IDE or not.
    * @throws CoreException Occurred Exception.
    */
   public void execute(IProgressMonitor monitor, boolean openCratedDiagram) throws CoreException, DSException {
      try {
         // Make sure that a connection is established.
         Assert.isTrue(connection.isConnected());
         // Clear old mapping
         mapping.clear();
         // Create resource
         TransactionalEditingDomain editingDomain = GMFEditingDomainFactory.INSTANCE.createEditingDomain();
         ResourceSet resourceSet = editingDomain.getResourceSet();
         final Resource resource = resourceSet.createResource(modelURI);
         // Create model
         final DbcModel model = DbcmodelFactory.eINSTANCE.createDbcModel();
         AbstractExceptionalRecordingCommand<DSException> cmd = new AbstractExceptionalRecordingCommand<DSException>(editingDomain) {
            @Override
            protected void doExecute() {
               try {
                  resource.getContents().add(model);
                  fillModel(model);
               }
               catch (DSException e) {
                  setException(e);
               }
            }
         };
         editingDomain.getCommandStack().execute(cmd);
         if (cmd.getException() != null) {
            throw cmd.getException();
         }
         // Save resource
         resource.save(Collections.EMPTY_MAP);
         initializeDiagram(editingDomain, diagramURI, model, openCratedDiagram);
      }
      catch (IOException e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus("Can't save model file:" + e.getMessage(), e));
      }      
   }
   
   /**
    * Fills the {@link DbcModel} with all information provided by the {@link IDSConnection}.
    * @param model The {@link DbcModel} to fill.
    * @throws DSException Occurred Exception
    */
   protected void fillModel(DbcModel model) throws DSException {
      // Add connection settings
      IDSDriver driver = connection.getDriver();
      if (driver != null) {
         model.setDriverId(driver.getId());
         Properties persitentProperties = driver.toPersistentProperties(connection.getConnectionSettings());
         Set<String> keys = persitentProperties.stringPropertyNames();
         for (String key : keys) {
            DbcProperty modelProperty = createDbcProperty(key, persitentProperties.getProperty(key));
            model.getConnectionSettings().add(modelProperty);
         }
      }
      // Create containment structure
      for (IDSPackage dsInstance : connection.getPackages()) {
         DbcPackage modelInstance = createDbcPackage(model, dsInstance);
         model.getPackages().add(modelInstance);
      }
      for (IDSClass dsInstance : connection.getClasses()) {
         DbcClass modelInstance = createDbcClass(model, dsInstance);
         model.getTypes().add(modelInstance);
      }
      for (IDSInterface dsInstance : connection.getInterfaces()) {
         DbcInterface modelInstance = createDbcInterface(model, dsInstance);
         model.getTypes().add(modelInstance);
      }
      for (IDSEnum dsInstance : connection.getEnums()) {
         DbcEnum modelInstance = createDbcEnum(model, dsInstance);
         model.getTypes().add(modelInstance);
      }
      // Set references (extends, implements)
      setReferencesInPackageTypes(connection.getPackages());
      setReferences(connection.getClasses());
      setReferences(connection.getInterfaces());
      setReferences(connection.getEnums());
   }

   /**
    * Iterates recursive over the packages to set the extends and implements references.
    * @param dsPackages The current {@link IDSPackage}s to iterate over.
    * @throws DSException Occurred Exception
    */
   protected void setReferencesInPackageTypes(List<IDSPackage> dsPackages) throws DSException {
      for (IDSPackage dsPackage : dsPackages) {
         setReferencesInPackageTypes(dsPackage.getPackages());
         setReferences(dsPackage.getClasses());
         setReferences(dsPackage.getInterfaces());
         setReferences(dsPackage.getEnums());
      }
   }
   
   /**
    * Sets recursive the extends and implements references in the given {@link IDSType}s.
    * @param <T> Type parameter.
    * @param dsTypes The current {@link IDSType}s.
    * @throws DSException Occurred Exception
    */
   protected <T extends IDSType> void setReferences(List<T> dsTypes) throws DSException {
      for (IDSType dsType : dsTypes) {
         setReferences(dsType.getInnerClasses());
         setReferences(dsType.getInnerInterfaces());
         setReferences(dsType.getInnerEnums());
         if (dsType instanceof IDSInterface) {
            IDSInterface dsInterface = (IDSInterface)dsType;
            AbstractDbcType dtcType = mapping.get(dsInterface);
            Assert.isTrue(dtcType instanceof DbcInterface);
            DbcInterface dbcInterface = (DbcInterface)dtcType;
            for (IDSInterface dsExtend : dsInterface.getExtends()) {
               AbstractDbcType dbcExtend = mapping.get(dsExtend);
               if (dbcExtend != null) {
                  Assert.isTrue(dbcExtend instanceof DbcInterface);
                  dbcInterface.getExtends().add((DbcInterface)dbcExtend);
               }
            }
            for (String fullName : dsInterface.getExtendsFullnames()) {
               dbcInterface.getExtendsFullNames().add(fullName);
            }
         }
         else if (dsType instanceof IDSClass) {
            IDSClass dsClass = (IDSClass)dsType;
            AbstractDbcType dtcType = mapping.get(dsClass);
            Assert.isTrue(dtcType instanceof DbcClass);
            DbcClass dbcClass = (DbcClass)dtcType;
            for (IDSClass dsExtend : dsClass.getExtends()) {
               AbstractDbcType dbcExtend = mapping.get(dsExtend);
               if (dbcExtend != null) {
                  Assert.isTrue(dbcExtend instanceof DbcClass);
                  dbcClass.getExtends().add((DbcClass)dbcExtend);
               }
            }
            for (String fullName : dsClass.getExtendsFullnames()) {
               dbcClass.getExtendsFullNames().add(fullName);
            }
            for (IDSInterface dsImplements : dsClass.getImplements()) {
               AbstractDbcType dbcImplements = mapping.get(dsImplements);
               if (dbcImplements != null) {
                  Assert.isTrue(dbcImplements instanceof DbcInterface);
                  dbcClass.getImplements().add((DbcInterface)dbcImplements);
               }
            }
            for (String fullName : dsClass.getImplementsFullnames()) {
               dbcClass.getImplementsFullNames().add(fullName);
            }
         }
         else if (dsType instanceof IDSEnum) {
            IDSEnum dsEnum = (IDSEnum)dsType;
            AbstractDbcType dtcType = mapping.get(dsEnum);
            Assert.isTrue(dtcType instanceof DbcEnum);
            DbcEnum dbcEnum = (DbcEnum)dtcType;
            for (IDSInterface dsImplements : dsEnum.getImplements()) {
               AbstractDbcType dbcImplements = mapping.get(dsImplements);
               if (dbcImplements != null) {
                  Assert.isTrue(dbcImplements instanceof DbcInterface);
                  dbcEnum.getImplements().add((DbcInterface)dbcImplements);
               }
            }
            for (String fullName : dsEnum.getImplementsFullnames()) {
               dbcEnum.getImplementsFullNames().add(fullName);
            }
         }
      }
   }
   
   /**
    * Fills the given {@link DbcInvariant} list with the attributes provided by the {@link IDSInvariant} list.
    * @param dbcInvariants The list to fill.
    * @param dsTypeInvariants The content to convert.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcInvariants(EList<DbcInvariant> dbcInvariants, List<IDSInvariant> dsTypeInvariants) throws DSException {
      for (IDSInvariant dsTypeInvariant : dsTypeInvariants) {
         DbcInvariant modelSpecificationInstance = createDbcInvariant(dsTypeInvariant);
         dbcInvariants.add(modelSpecificationInstance);
      }
   }
   
   /**
    * Fills the given {@link DbcAxiom} list with the attributes provided by the {@link IDSAxiom} list.
    * @param dbcAxioms The list to fill.
    * @param dsAxioms The content to convert.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcAxioms(DbcModel dbcModel, EList<DbcAxiom> dbcAxioms, List<IDSAxiom> dsAxioms) throws DSException {
      for (IDSAxiom dsAxiom : dsAxioms) {
         DbcAxiom modelSpecificationInstance = createDbcAxiom(dbcModel, dsAxiom);
         dbcAxioms.add(modelSpecificationInstance);
      }
   }

   /**
    * Fills the given {@link DbCAxiomContract} list with the attributes provided by the {@link IDSAxiomContract} list.
    * @param dbcAxiomContracts The list to fill.
    * @param dsAxiomContracts The content to convert.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcAxiomContracts(DbcModel dbcModel, EList<DbCAxiomContract> dbcAxiomContracts, List<IDSAxiomContract> dsAxiomContracts) throws DSException {
      for (IDSAxiomContract dsAxiomContract : dsAxiomContracts) {
         DbCAxiomContract modelSpecificationInstance = createDbcAxiomContract(dbcModel, dsAxiomContract);
         dbcAxiomContracts.add(modelSpecificationInstance);
      }
   }

   /**
    * Fills the given {@link DbcOperationContract} list with the attributes provided by the {@link IDSOperationContract} list.
    * @param dbcOperationContracts The list to fill.
    * @param dsOperationContracts The content to convert.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcOperationContracts(DbcModel dbcModel, EList<DbcOperationContract> dbcOperationContracts, List<IDSOperationContract> dsOperationContracts) throws DSException {
      for (IDSOperationContract dsOperationContract : dsOperationContracts) {
         DbcOperationContract modelSpecificationInstance = createDbcOperationContract(dbcModel, dsOperationContract);
         dbcOperationContracts.add(modelSpecificationInstance);
      }
   }

   /**
    * Fills the given {@link DbcAttribute} list with the attributes provided by the {@link IDSAttribute} list.
    * @param dbcAttributes The list to fill.
    * @param dsAttributes The content to convert.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcAttributes(List<DbcAttribute> dbcAttributes, List<IDSAttribute> dsAttributes) throws DSException {
      for (IDSAttribute dsAtttributeInstance : dsAttributes) {
         DbcAttribute modelAttributeInstance = createDbcAttribute(dsAtttributeInstance);
         dbcAttributes.add(modelAttributeInstance);
      }
   }
   
   /**
    * Fills the given {@link DbcMethod} list with the attributes provided by the {@link IDSMethod} list.
    * @param dbcMethods The list to fill.
    * @param dsMethods The content to convert.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcMethods(DbcModel dbcModel, List<DbcMethod> dbcMethods, List<IDSMethod> dsMethods) throws DSException {
      for (IDSMethod dsMethodInstance : dsMethods) {
         DbcMethod modelMethodInstance = createDbcMethod(dbcModel, dsMethodInstance);
         dbcMethods.add(modelMethodInstance);
      }
   }
   
   /**
    * Fills the given {@link DbcConstructor} list with the attributes provided by the {@link IDSConstructor} list.
    * @param dbcConstructors The list to fill.
    * @param dsConstructors The content to convert.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcConstructors(DbcModel dbcModel, List<DbcConstructor> dbcConstructors, List<IDSConstructor> dsConstructors) throws DSException {
      for (IDSConstructor dsConstructorInstance : dsConstructors) {
         DbcConstructor modelConstructorInstance = createDbcConstructor(dbcModel, dsConstructorInstance);
         dbcConstructors.add(modelConstructorInstance);
      }
   }
   
   /**
    * Fills the given {@link DbcEnumLiteral} list with the attributes provided by the {@link IDSEnumLiteral} list.
    * @param dbcEnumLiteral The list to fill.
    * @param dsEnumLiteral The content to convert.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcEnumLiterals(List<DbcEnumLiteral> dbcEnumLiteral, List<IDSEnumLiteral> dsEnumLiteral) throws DSException {
      for (IDSEnumLiteral dsEnumLiteralInstance : dsEnumLiteral) {
         DbcEnumLiteral modelEnumLiteralInstance = createDbcEnumLiteral(dsEnumLiteralInstance);
         dbcEnumLiteral.add(modelEnumLiteralInstance);
      }
   }

   /**
    * Adds inner classes, interfaces and enumerations to the given type.
    * @param dsType The type to fill.
    * @param dbcType The content to add.
    * @throws DSException Occurred Exception
    */
   protected void fillDbcType(DbcModel dbcModel, IDSType dsType, AbstractDbcType dbcType) throws DSException {
      for (IDSClass dsClassInstance : dsType.getInnerClasses()) {
         DbcClass modelClassInstance = createDbcClass(dbcModel, dsClassInstance);
         dbcType.getTypes().add(modelClassInstance);
      }
      for (IDSInterface dsInterfaceInstance : dsType.getInnerInterfaces()) {
         DbcInterface modelInterfaceInstance = createDbcInterface(dbcModel, dsInterfaceInstance);
         dbcType.getTypes().add(modelInterfaceInstance);
      }
      for (IDSEnum dsEnumInstance : dsType.getInnerEnums()) {
         DbcEnum modelEnumInstance = createDbcEnum(dbcModel, dsEnumInstance);
         dbcType.getTypes().add(modelEnumInstance);
      }
   }

   /**
    * Creates a {@link DbcEnum} and sets the values provided by the {@link IDSEnum}.
    * @param dsInstance The {@link IDSEnum} that provides the values.
    * @return The created {@link DbcEnum}.
    * @throws DSException Occurred Exception
    */
   protected DbcEnum createDbcEnum(DbcModel dbcModel, IDSEnum dsInstance) throws DSException {
      Assert.isNotNull(dsInstance);
      DbcEnum modelInstance = DbcmodelFactory.eINSTANCE.createDbcEnum();
      mapping.put(dsInstance, modelInstance);
      modelInstance.setName(dsInstance.getName());
      modelInstance.setStatic(dsInstance.isStatic());
      Assert.isNotNull(dsInstance.getVisibility());
      modelInstance.setVisibility(toDbc(dsInstance.getVisibility()));
      fillDbcType(dbcModel, dsInstance, modelInstance);
      fillDbcProvable(dbcModel, dsInstance, modelInstance);
      fillDbcAttributes(modelInstance.getAttributes(), dsInstance.getAttributes());
      fillDbcMethods(dbcModel, modelInstance.getMethods(), dsInstance.getMethods());
      fillDbcConstructors(dbcModel, modelInstance.getConstructors(), dsInstance.getConstructors());
      fillDbcEnumLiterals(modelInstance.getLiterals(), dsInstance.getLiterals());
      fillDbcInvariants(modelInstance.getInvariants(), dsInstance.getInvariants());
      fillDbcAxioms(dbcModel, modelInstance.getAxioms(), dsInstance.getAxioms());
      return modelInstance;
   }
   
   /**
    * Creates a {@link DbcInterface} and sets the values provided by the {@link IDSInterface}.
    * @param dsInstance The {@link IDSInterface} that provides the values.
    * @return The created {@link DbcInterface}.
    * @throws DSException Occurred Exception
    */
   protected DbcInterface createDbcInterface(DbcModel dbcModel, IDSInterface dsInstance) throws DSException {
      Assert.isNotNull(dsInstance);
      DbcInterface modelInstance = DbcmodelFactory.eINSTANCE.createDbcInterface();
      mapping.put(dsInstance, modelInstance);
      modelInstance.setName(dsInstance.getName());
      modelInstance.setStatic(dsInstance.isStatic());
      Assert.isNotNull(dsInstance.getVisibility());
      modelInstance.setVisibility(toDbc(dsInstance.getVisibility()));
      fillDbcProvable(dbcModel, dsInstance, modelInstance);
      fillDbcType(dbcModel, dsInstance, modelInstance);
      fillDbcAttributes(modelInstance.getAttributes(), dsInstance.getAttributes());
      fillDbcMethods(dbcModel, modelInstance.getMethods(), dsInstance.getMethods());
      fillDbcInvariants(modelInstance.getInvariants(), dsInstance.getInvariants());
      fillDbcAxioms(dbcModel, modelInstance.getAxioms(), dsInstance.getAxioms());
      return modelInstance;
   }
   
   /**
    * Creates a {@link DbcClass} and sets the values provided by the {@link IDSClass}.
    * @param dsInstance The {@link IDSClass} that provides the values.
    * @return The created {@link DbcClass}.
    * @throws DSException Occurred Exception
    */
   protected DbcClass createDbcClass(DbcModel dbcModel, IDSClass dsInstance) throws DSException {
      Assert.isNotNull(dsInstance);
      DbcClass modelInstance = DbcmodelFactory.eINSTANCE.createDbcClass();
      mapping.put(dsInstance, modelInstance);
      modelInstance.setAnonymous(dsInstance.isAnonymous());
      modelInstance.setAbstract(dsInstance.isAbstract());
      modelInstance.setFinal(dsInstance.isFinal());
      modelInstance.setName(dsInstance.getName());
      modelInstance.setStatic(dsInstance.isStatic());
      modelInstance.setVisibility(toDbc(dsInstance.getVisibility()));
      fillDbcProvable(dbcModel, dsInstance, modelInstance);
      fillDbcType(dbcModel, dsInstance, modelInstance);
      fillDbcAttributes(modelInstance.getAttributes(), dsInstance.getAttributes());
      fillDbcMethods(dbcModel, modelInstance.getMethods(), dsInstance.getMethods());
      fillDbcConstructors(dbcModel, modelInstance.getConstructors(), dsInstance.getConstructors());
      fillDbcInvariants(modelInstance.getInvariants(), dsInstance.getInvariants());
      fillDbcAxioms(dbcModel, modelInstance.getAxioms(), dsInstance.getAxioms());
      return modelInstance;
   }

   /**
    * Fills the provable.
    * @param dbcModel The provable to fill.
    * @param dsProvable The provable that provides the content.
    * @param dbcProvable The {@link DbcModel} that contains proof obligations.
    * @throws DSException Occurred Exception.
    */
   protected void fillDbcProvable(DbcModel dbcModel, IDSProvable dsProvable, IDbCProvable dbcProvable) throws DSException {
      Assert.isNotNull(dsProvable);
      Assert.isNotNull(dsProvable.getObligations());
      Assert.isNotNull(dbcProvable);
      for (String obligation : dsProvable.getObligations()) {
         DbcProofObligation dbcObligation = dbcModel.getProofObligation(obligation);
         if (dbcObligation == null) {
            dbcObligation = DbcmodelFactory.eINSTANCE.createDbcProofObligation();
            dbcObligation.setObligation(obligation);
            dbcModel.getProofObligations().add(dbcObligation);
         }
         dbcProvable.getProofObligations().add(dbcObligation);
      }
   }

   /**
    * Creates a {@link DbcConstructor} and sets the values provided by the {@link IDSConstructor}.
    * @param dsConstructorInstance The {@link IDSConstructor} that provides the values.
    * @return The created {@link DbcConstructor}.
    * @throws DSException Occurred Exception
    */
   protected DbcConstructor createDbcConstructor(DbcModel dbcModel, IDSConstructor dsConstructorInstance) throws DSException {
      Assert.isNotNull(dsConstructorInstance);
      DbcConstructor modelInstance = DbcmodelFactory.eINSTANCE.createDbcConstructor();
      modelInstance.setSignature(dsConstructorInstance.getSignature());
      modelInstance.setStatic(dsConstructorInstance.isStatic());
      Assert.isNotNull(dsConstructorInstance.getVisibility());
      modelInstance.setVisibility(toDbc(dsConstructorInstance.getVisibility()));
      fillDbcProvable(dbcModel, dsConstructorInstance, modelInstance);
      fillDbcOperationContracts(dbcModel, modelInstance.getOperationContracts(), dsConstructorInstance.getOperationContracts());
      return modelInstance;
   }

   /**
    * Creates a {@link DbcMethod} and sets the values provided by the {@link IDSMethod}.
    * @param dsMethodInstance The {@link IDSMethod} that provides the values.
    * @return The created {@link DbcMethod}.
    * @throws DSException Occurred Exception
    */
   protected DbcMethod createDbcMethod(DbcModel dbcModel, IDSMethod dsMethodInstance) throws DSException {
      Assert.isNotNull(dsMethodInstance);
      DbcMethod modelInstance = DbcmodelFactory.eINSTANCE.createDbcMethod();
      modelInstance.setAbstract(dsMethodInstance.isAbstract());
      modelInstance.setFinal(dsMethodInstance.isFinal());
      modelInstance.setSignature(dsMethodInstance.getSignature());
      modelInstance.setReturnType(dsMethodInstance.getReturnType());
      modelInstance.setStatic(dsMethodInstance.isStatic());
      Assert.isNotNull(dsMethodInstance.getVisibility());
      modelInstance.setVisibility(toDbc(dsMethodInstance.getVisibility()));
      fillDbcProvable(dbcModel, dsMethodInstance, modelInstance);
      fillDbcOperationContracts(dbcModel, modelInstance.getOperationContracts(), dsMethodInstance.getOperationContracts());
      return modelInstance;
   }

   /**
    * Creates a {@link DbcEnumLiteral} and sets the values provided by the {@link IDSEnumLiteral}.
    * @param dsEnumLiteralInstance The {@link IDSEnumLiteral} that provides the values.
    * @return The created {@link DbcEnumLiteral}.
    * @throws DSException Occurred Exception
    */
   protected DbcEnumLiteral createDbcEnumLiteral(IDSEnumLiteral dsEnumLiteralInstance) throws DSException {
      Assert.isNotNull(dsEnumLiteralInstance);
      DbcEnumLiteral modelInstance = DbcmodelFactory.eINSTANCE.createDbcEnumLiteral();
      modelInstance.setName(dsEnumLiteralInstance.getName());
      return modelInstance;
   }
   
   /**
    * Creates an {@link DbcProperty} with the given key value pair.
    * @param key The key to use.
    * @param value The value to use.
    * @return The created {@link DbcProperty}.
    */
   protected DbcProperty createDbcProperty(String key, String value) {
      DbcProperty modelInstance = DbcmodelFactory.eINSTANCE.createDbcProperty();
      modelInstance.setKey(key);
      modelInstance.setValue(value);
      return modelInstance;
   }

   /**
    * Creates a {@link DbcAttribute} and sets the values provided by the {@link IDSAttribute}.
    * @param dsAttributeInstance The {@link IDSAttribute} that provides the values.
    * @return The created {@link DbcAttribute}.
    * @throws DSException Occurred Exception
    */
   protected DbcAttribute createDbcAttribute(IDSAttribute dsAttributeInstance) throws DSException {
      Assert.isNotNull(dsAttributeInstance);
      DbcAttribute modelInstance = DbcmodelFactory.eINSTANCE.createDbcAttribute();
      modelInstance.setFinal(dsAttributeInstance.isFinal());
      modelInstance.setName(dsAttributeInstance.getName());
      modelInstance.setType(dsAttributeInstance.getType());
      modelInstance.setStatic(dsAttributeInstance.isStatic());
      Assert.isNotNull(dsAttributeInstance.getVisibility());
      modelInstance.setVisibility(toDbc(dsAttributeInstance.getVisibility()));
      return modelInstance;
   }
   
   /**
    * Creates a {@link DbcInvariant} and sets the values provided by the {@link IDSInvariant}.
    * @param dsTypeInvariant The {@link IDSInvariant} that provides the values.
    * @return The created {@link DbcInvariant}.
    * @throws DSException Occurred Exception
    */
   protected DbcInvariant createDbcInvariant(IDSInvariant dsTypeInvariant) throws DSException {
      Assert.isNotNull(dsTypeInvariant);
      DbcInvariant modelInstance = DbcmodelFactory.eINSTANCE.createDbcInvariant();
      modelInstance.setName(dsTypeInvariant.getName());
      modelInstance.setCondition(dsTypeInvariant.getCondition());
      return modelInstance;
   }
   
   /**
    * Creates a {@link DbcAxiom} and sets the values provided by the {@link IDSAxiom}.
    * @param dsAxiom The {@link IDSAxiom} that provides the values.
    * @return The created {@link DbcAxiom}.
    * @throws DSException Occurred Exception
    */
   protected DbcAxiom createDbcAxiom(DbcModel dbcModel, IDSAxiom dsAxiom) throws DSException {
      Assert.isNotNull(dsAxiom);
      DbcAxiom modelInstance = DbcmodelFactory.eINSTANCE.createDbcAxiom();
      modelInstance.setName(dsAxiom.getName());
      modelInstance.setDefinition(dsAxiom.getDefinition());
      fillDbcAxiomContracts(dbcModel, modelInstance.getAxiomContracts(), dsAxiom.getAxiomContracts());
      return modelInstance;
   }

   /**
    * Creates a {@link DbCAxiomContract} and sets the values provided by the {@link IDSAxiomContract}.
    * @param dsAxiomContract The {@link IDSAxiomContract} that provides the values.
    * @return The created {@link DbCAxiomContract}.
    * @throws DSException Occurred Exception
    */
   protected DbCAxiomContract createDbcAxiomContract(DbcModel dbcModel, IDSAxiomContract dsAxiomContract) throws DSException {
      Assert.isNotNull(dsAxiomContract);
      DbCAxiomContract modelInstance = DbcmodelFactory.eINSTANCE.createDbCAxiomContract();
      fillDbcProvable(dbcModel, dsAxiomContract, modelInstance);
      modelInstance.setName(dsAxiomContract.getName());
      modelInstance.setDep(dsAxiomContract.getDep());
      modelInstance.setPre(dsAxiomContract.getPre());
      return modelInstance;
   }

   /**
    * Creates a {@link DbcOperationContract} and sets the values provided by the {@link IDSOperationContract}.
    * @param dsOperationContract The {@link IDSOperationContract} that provides the values.
    * @return The created {@link DbcOperationContract}.
    * @throws DSException Occurred Exception
    */
   protected DbcOperationContract createDbcOperationContract(DbcModel dbcModel, IDSOperationContract dsOperationContract) throws DSException {
      Assert.isNotNull(dsOperationContract);
      DbcOperationContract modelInstance = DbcmodelFactory.eINSTANCE.createDbcOperationContract();
      fillDbcProvable(dbcModel, dsOperationContract, modelInstance);
      modelInstance.setModifies(dsOperationContract.getModifies());
      modelInstance.setName(dsOperationContract.getName());
      modelInstance.setPost(dsOperationContract.getPost());
      modelInstance.setPre(dsOperationContract.getPre());
      modelInstance.setTermination(dsOperationContract.getTermination());
      return modelInstance;
   }

   /**
    * Creates a {@link DbcPackage} and sets the values provided by the {@link IDSPackage}.
    * @param dsInstance The {@link IDSPackage} that provides the values.
    * @return The created {@link DbcPackage}.
    * @throws DSException Occurred Exception
    */
   protected DbcPackage createDbcPackage(DbcModel dbcModel, IDSPackage dsInstance) throws DSException {
      Assert.isNotNull(dsInstance);
      DbcPackage modelInstance = DbcmodelFactory.eINSTANCE.createDbcPackage();
      modelInstance.setName(dsInstance.getName());
      for (IDSPackage dsPackage : dsInstance.getPackages()) {
         DbcPackage dbcPackage = createDbcPackage(dbcModel, dsPackage);
         modelInstance.getPackages().add(dbcPackage);
      }
      for (IDSClass dsClassInstance : dsInstance.getClasses()) {
         DbcClass modelClassInstance = createDbcClass(dbcModel, dsClassInstance);
         modelInstance.getTypes().add(modelClassInstance);
      }
      for (IDSInterface dsInterfaceInstance : dsInstance.getInterfaces()) {
         DbcInterface modelInterfaceInstance = createDbcInterface(dbcModel, dsInterfaceInstance);
         modelInstance.getTypes().add(modelInterfaceInstance);
      }
      for (IDSEnum dsEnumInstance : dsInstance.getEnums()) {
         DbcEnum modelEnumInstance = createDbcEnum(dbcModel, dsEnumInstance);
         modelInstance.getTypes().add(modelEnumInstance);
      }
      return modelInstance;
   }
   
   /**
    * Converts the given {@link DSVisibility} into a {@link DbcVisibility}.
    * @param visibility The {@link DSVisibility} to convert.
    * @return The same literal as {@link DbcVisibility}.
    */
   public static DbcVisibility toDbc(DSVisibility visibility) {
      if (visibility != null) {
         switch (visibility) {
            case PRIVATE : return DbcVisibility.PRIVATE;
            case PROTECTED : return DbcVisibility.PROTECTED;
            case PUBLIC : return DbcVisibility.PUBLIC;
            default : return DbcVisibility.DEFAULT;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Copied code from {@link DbcModelNewDiagramFileWizard#performFinish()}
    */
   protected void initializeDiagram(TransactionalEditingDomain myEditingDomain,
                                    URI diagramModelURI, 
                                    final EObject rootElement,
                                    boolean openCratedDiagram) {
      LinkedList<IFile> affectedFiles = new LinkedList<IFile>();
      // IFile diagramFile = myFileCreationPage.createNewFile();
//      DbcModelDiagramEditorUtil.setCharset(diagramFile);
//      affectedFiles.add(diagramFile);
//      URI diagramModelURI = URI.createPlatformResourceURI(diagramFile.getFullPath().toString(), true);
      ResourceSet resourceSet = myEditingDomain.getResourceSet();
      final Resource diagramResource = resourceSet.createResource(diagramModelURI);
      AbstractTransactionalCommand command = new AbstractTransactionalCommand(myEditingDomain, Messages.DbCNewDiagramFileWizard_InitDiagramCommand, affectedFiles) {
         protected CommandResult doExecuteWithResult(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
            // int diagramVID = DbcModelVisualIDRegistry
            // .getDiagramVisualID(diagramRootElementSelectionPage
            // .getModelElement());
            int diagramVID = 1000;
            if (diagramVID != DbcModelEditPart.VISUAL_ID) {
               return CommandResult.newErrorCommandResult(Messages.DbCNewDiagramFileWizard_IncorrectRootError);
            }
            Diagram diagram = ViewService.createDiagram(rootElement, // diagramRootElementSelectionPage.getModelElement(),
                                                        DbcModelEditPart.MODEL_ID,
                                                        DbCDiagramEditorPlugin.DIAGRAM_PREFERENCES_HINT);
            diagramResource.getContents().add(diagram);
            return CommandResult.newOKCommandResult();
         }
      };
      try {
         OperationHistoryFactory.getOperationHistory().execute(command, new NullProgressMonitor(), null);
         diagramResource.save(DbCDiagramEditorUtil.getSaveOptions());
         if (openCratedDiagram) {
            Display.getDefault().asyncExec(new Runnable() {
               @Override
               public void run() {
                  try {
                     DbCDiagramEditorUtil.openDiagram(diagramResource);
                  }
                  catch (PartInitException ex) {
                     DbCDiagramEditorPlugin.getInstance().logError("Unable to open editor", ex); //$NON-NLS-1$
                  }
               }
            });
         }
      }
      catch (ExecutionException e) {
         DbCDiagramEditorPlugin.getInstance().logError("Unable to create model and diagram", e); //$NON-NLS-1$
      }
      catch (IOException ex) {
         DbCDiagramEditorPlugin.getInstance().logError("Save operation failed for: " + diagramModelURI, ex); //$NON-NLS-1$
      }
   }
}