/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package de.hentschel.visualdbc.key.ui.util;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.key.intern.helper.KeyHacks;
import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.rule.KeyProofReferenceUtil;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation;
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
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcProofStatus;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;

/**
 * This classed is used to create a minimal {@link DbcModel} which shows
 * the references between a given {@link Proof} an the target of 
 * {@link IProofReference} added via {@link #updateModel(LinkedHashSet, IProgressMonitor)}.
 * @author Martin Hentschel
 */
public class ProofReferenceModelCreator {
   /**
    * Maps a {@link Proof} to its representation in {@link #dbcModel}.
    */
   private Map<Proof, DbcProof> proofMapping = new HashMap<Proof, DbcProof>();

   /**
    * Maps a {@link KeYJavaType} to its representation in {@link #dbcModel}.
    */
   private Map<KeYJavaType, AbstractDbcType> typeMapping = new HashMap<KeYJavaType, AbstractDbcType>();

   /**
    * Maps an {@link IProgramVariable} to its representation in {@link #dbcModel}.
    */
   private Map<IProgramVariable, DbcAttribute> attributeMapping = new HashMap<IProgramVariable, DbcAttribute>();

   /**
    * Maps an {@link IProgramVariable} to its representation in {@link #dbcModel}.
    */
   private Map<IProgramVariable, DbcEnumLiteral> literalMapping = new HashMap<IProgramVariable, DbcEnumLiteral>();

   /**
    * Maps an {@link IProgramMethod} to its representation in {@link #dbcModel}.
    */
   private Map<IProgramMethod, AbstractDbcOperation> operationMapping = new HashMap<IProgramMethod, AbstractDbcOperation>();

   /**
    * Maps a {@link FunctionalOperationContract} to its representation in {@link #dbcModel}.
    */
   private Map<FunctionalOperationContract, DbcOperationContract> operationContractMapping = new HashMap<FunctionalOperationContract, DbcOperationContract>();

   /**
    * Maps a {@link ClassInvariant} to its representation in {@link #dbcModel}.
    */
   private Map<ClassInvariant, DbcInvariant> invariantMapping = new HashMap<ClassInvariant, DbcInvariant>();

   /**
    * Maps a {@link ClassAxiom} to its representation in {@link #dbcModel}.
    */
   private Map<ClassAxiom, DbcAxiom> axiomMapping = new HashMap<ClassAxiom, DbcAxiom>();

   /**
    * Maps a {@link DependencyContract} to its representation in {@link #dbcModel}.
    */
   private Map<DependencyContract, DbCAxiomContract> axiomContractMapping = new HashMap<DependencyContract, DbCAxiomContract>();

   /**
    * Maps an {@link IProofReference} to its representation in {@link #dbcModel}.
    */
   private Map<IProofReference<?>, DbcProofReference> proofReferenceMapping = new HashMap<IProofReference<?>, DbcProofReference>();
   
   /**
    * Maps a {@link Proof} to its {@link Services}to avoid problems if {@link #proof} is disposed while {@link #updateModel(LinkedHashSet, IProgressMonitor)} is active.
    */
   private Map<Proof, Services> servicesMapping = new HashMap<Proof, Services>();
   
   /**
    * The maintained {@link DbcModel}.
    */
   private DbcModel dbcModel;
   
   /**
    * Constructor.
    * @param proofs The {@link Proofs} which references should be shown by the maintained {@link DbcModel}.
    * @throws DSException Occurred Exception.
    */
   public ProofReferenceModelCreator(Proof... proofs) throws DSException {
      // Init references
      Assert.isNotNull(proofs);
      for (Proof proof : proofs) {
         Services services = proof.getServices(); 
         Assert.isNotNull(services);
         servicesMapping.put(proof, services);
      }
      // Create model
      this.dbcModel = DbcmodelFactory.eINSTANCE.createDbcModel();
      // Make sure that proofs exist
      for (Proof proof : proofs) {
         makeSureProofExist(proof, getServices(proof));
      }
   }
   
   /**
    * Returns the {@link Services} of the given {@link Proof}.
    * @param proof The {@link Proof} for which the {@link Services} are requested.
    * @return The {@link Services} of the given {@link Proof}.
    */
   public Services getServices(Proof proof) {
      return servicesMapping.get(proof);
   }
   
   /**
    * Updates the managed {@link DbcModel} and makes sure that the given
    * {@link IProofReference} instances are added to it.
    * @param references The {@link IProofReference}s to add.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DSException Occurred Exception.
    */
   public void updateModel(LinkedHashSet<IProofReference<?>> references, IProgressMonitor monitor) throws DSException {
      SWTUtil.checkCanceled(monitor);
      monitor.beginTask("Analyzing found proof references", references.size());
      for (IProofReference<?> reference : references) {
         SWTUtil.checkCanceled(monitor);
         Proof proof = reference.getSource();
         if (proof == null) {
            throw new DSException("Reference \"" + reference + "\" has no source proof.");
         }
         DbcProof dbcProof = proofMapping.get(proof);
         if (dbcProof == null) {
            throw new DSException("Proof \"" + proof + "\" is not supported.");
         }
         makeSureProofReferenceExist(reference, getServices(proof), dbcProof);
         monitor.worked(1);
      }
      monitor.done();
   }
   
   /**
    * Returns the created {@link DbcModel}.
    * @return The created {@link DbcModel}.
    */
   public DbcModel getModel() {
      return dbcModel;
   }

   /**
    * Makes sure that the given {@link Proof} is part of the {@link DbcModel}.
    * @param proof The {@link Proof} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link DbcProof} which represents the given {@link Proof}.
    * @throws DSException Occurred Exception.
    */
   protected DbcProof makeSureProofExist(Proof proof, Services services) throws DSException {
      DbcProof result = proofMapping.get(proof);
      if (result == null) {
         // Create Proof
         result = DbcmodelFactory.eINSTANCE.createDbcProof();
         result.setObligation(KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT);
         if (proof.closed()) {
            result.setStatus(DbcProofStatus.FULFILLED);
         }
         else {
            result.setStatus(DbcProofStatus.OPEN);
         }
         dbcModel.getProofs().add(result);
         // Create Proof target
         ProofOblInput input = getServices(proof).getSpecificationRepository().getProofOblInput(proof);
         if (input instanceof ContractPO) {
            Contract contract = ((ContractPO) input).getContract();
            if (contract instanceof FunctionalOperationContract) {
               DbcOperationContract dbcContract = makeSureOperationContractExist((FunctionalOperationContract)contract, services);
               if (dbcContract != null) {
                  result.setTarget(dbcContract);
               }
            }
            else if (contract instanceof DependencyContract) {
               DbCAxiomContract dbcContract = makeSureAxiomContractExist((DependencyContract)contract, services);
               if (dbcContract != null) {
                  result.setTarget(dbcContract);
               }
            }
            else {
               throw new DSException("Contract \"" + contract + "\" is not supported.");
            }
         }
         else if (input instanceof ProgramMethodPO) {
            IProgramMethod pm = ((ProgramMethodPO) input).getProgramMethod();
            AbstractDbcOperation dbcOperation = makeSureOperationExist(pm, services);
            if (dbcOperation != null) {
               result.setTarget(dbcOperation);
            }
         }
         else {
            throw new DSException("Problem \"" + input + "\" is not supported.");
         }
         proofMapping.put(proof, result);
      }
      return result;
   }

   /**
    * Makes sure that the given {@link IProofReference} is part of the {@link DbcModel}.
    * @param reference The {@link IProofReference} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @param dbcProof The {@link DbcProof} which is the source of the {@link DbcProofReference}.
    * @return The {@link DbcProofReference} which represents the given {@link IProofReference}.
    * @throws DSException Occurred Exception.
    */
   protected DbcProofReference makeSureProofReferenceExist(IProofReference<?> reference, Services services, DbcProof dbcProof) throws DSException {
      DbcProofReference result = proofReferenceMapping.get(reference);
      if (result == null) {
         IDbCProofReferencable dbcReferencable = null;
         if (reference.getTarget() instanceof IProgramMethod) {
            IProgramMethod pm = (IProgramMethod)reference.getTarget();
            if (KeYTypeUtil.isImplicitConstructor(pm)) {
               pm = KeYTypeUtil.findExplicitConstructor(services, pm);
            }
            if (pm != null) {
               dbcReferencable = makeSureOperationExist(pm, services);
            }
         }
         else if (reference.getTarget() instanceof IProgramVariable) {
            IProgramVariable pv = (IProgramVariable)reference.getTarget();
            if (EnumClassDeclaration.isEnumConstant(pv)) {
               dbcReferencable = makeSureLiteralExist(pv, services);
            }
            else {
               dbcReferencable = makeSureAttributeExist(pv, services);
            }
         }
         else if (reference.getTarget() instanceof ClassAxiom) {
            dbcReferencable = makeSureAxiomExist((ClassAxiom)reference.getTarget(), services);
         }
         else if (reference.getTarget() instanceof ClassInvariant) {
            dbcReferencable = makeSureInvariantExist((ClassInvariant)reference.getTarget(), services);
         }
         else if (reference.getTarget() instanceof Contract) {
            if (reference.getTarget() instanceof FunctionalOperationContract) {
               dbcReferencable = makeSureOperationContractExist((FunctionalOperationContract)reference.getTarget(), services);
            }
            else if (reference.getTarget() instanceof DependencyContract) {
               dbcReferencable = makeSureAxiomContractExist((DependencyContract)reference.getTarget(), services);
            }
            else {
               throw new DSException("Contract \"" + reference.getTarget() + "\" is not supported.");
            }
         }
         else {
            throw new DSException("Proof Reference \"" + reference + "\" is not supported.");
         }
         if (dbcReferencable != null) {
            result = DbcmodelFactory.eINSTANCE.createDbcProofReference();
            result.setKind(toDbcReferenceKind(reference.getKind()));
            result.setSource(dbcProof);
            result.setTarget(dbcReferencable);
            dbcProof.getProofReferences().add(result);
         }
      }
      return result;
   }

   /**
    * Converts the given {@link IProofReference#getKind()} value into
    * the kind name of the {@link KeyProofReferenceUtil}.
    * @param kind The kind to convert.
    * @return The converted value
    * @throws DSException Occurred Exception.
    */
   protected String toDbcReferenceKind(String kind) throws DSException {
      if (IProofReference.ACCESS.equals(kind)) {
         return KeyProofReferenceUtil.ACCESS;
      }
      else if (IProofReference.CALL_METHOD.equals(kind)) {
         return KeyProofReferenceUtil.CALL_METHOD;
      }
      else if (IProofReference.INLINE_METHOD.equals(kind)) {
         return KeyProofReferenceUtil.INLINE_METHOD;
      }
      else if (IProofReference.USE_AXIOM.equals(kind)) {
         return KeyProofReferenceUtil.USE_AXIOM;
      }
      else if (IProofReference.USE_CONTRACT.equals(kind)) {
         return KeyProofReferenceUtil.USE_CONTRACT;
      }
      else if (IProofReference.USE_INVARIANT.equals(kind)) {
         return KeyProofReferenceUtil.USE_INVARIANT;
      }
      else {
         throw new DSException("Proof reference kind \"" + kind+ "\" is not supported.");
      }
   }

   /**
    * Makes sure that the given {@link FunctionalOperationContract} is part of the {@link DbcModel}.
    * @param contract The {@link FunctionalOperationContract} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link DbcOperationContract} which represents the given {@link FunctionalOperationContract}.
    * @throws DSException Occurred Exception.
    */
   protected DbcOperationContract makeSureOperationContractExist(FunctionalOperationContract contract, Services services) throws DSException {
      if (contract.getTarget() instanceof IProgramMethod) {
         DbcOperationContract result = operationContractMapping.get(contract);
         if (result == null) {
            AbstractDbcOperation dbcOperation = makeSureOperationExist((IProgramMethod)contract.getTarget(), services);
            if (dbcOperation != null) {
               result = DbcmodelFactory.eINSTANCE.createDbcOperationContract();
               result.setModifies(KeyHacks.getOperationContractModifies(services, contract));
               result.setName(contract.getName());
               result.setPost(KeyHacks.getOperationContractPost(services, contract));
               result.setPre(KeyHacks.getOperationContractPre(services, contract));
               result.setTermination(ObjectUtil.toString(contract.getModality()));
               dbcOperation.getOperationContracts().add(result);
               operationContractMapping.put(contract, result);
            }
         }
         return result;
      }
      else {
         throw new DSException("Target of contract \"" + contract + "\" is not supported.");
      }
   }

   /**
    * Makes sure that the given {@link DependencyContract} is part of the {@link DbcModel}.
    * @param contract The {@link DependencyContract} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link DbCAxiomContract} which represents the given {@link DependencyContract}.
    * @throws DSException Occurred Exception.
    */
   protected DbCAxiomContract makeSureAxiomContractExist(final DependencyContract contract, final Services services) throws DSException {
      ClassAxiom ca;
      if (contract.getTarget() instanceof ClassAxiom) {
         ca = (ClassAxiom)contract.getTarget();
      }
      else {
         ImmutableSet<ClassAxiom> axioms = services.getSpecificationRepository().getClassAxioms(contract.getKJT());
         ca = CollectionUtil.search(axioms, new IFilter<ClassAxiom>() {
            @Override
            public boolean select(ClassAxiom element) {
               return KeyConnection.shouldIncludeClassAxiom(services, element.getKJT(), element) &&
                      ObjectUtil.equals(contract.getTarget(), element.getTarget());
            }
         });
      }
      if (ca != null) {
         DbCAxiomContract result = axiomContractMapping.get(contract);
         if (result == null) {
            DbcAxiom dbcAxiom = makeSureAxiomExist(ca, services);
            if (dbcAxiom != null) {
               result = DbcmodelFactory.eINSTANCE.createDbCAxiomContract();
               result.setDep(KeyHacks.getDependencyContractDep(services, contract));
               result.setName(contract.getName());
               result.setPre(KeyHacks.getOperationContractPre(services, contract));
               dbcAxiom.getAxiomContracts().add(result);
               axiomContractMapping.put(contract, result);
            }
         }
         return result;
      }
      else {
         throw new DSException("Target of contract \"" + contract + "\" is not supported.");
      }
   }

   /**
    * Makes sure that the given {@link IProgramMethod} is part of the {@link DbcModel}.
    * @param pm The {@link IProgramMethod} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link AbstractDbcOperation} which represents the given {@link IProgramMethod}.
    * @throws DSException Occurred Exception.
    */
   protected AbstractDbcOperation makeSureOperationExist(IProgramMethod pm, Services services) throws DSException {
      if (!pm.isImplicit()) {
         AbstractDbcOperation result = operationMapping.get(pm);
         if (result == null) {
            AbstractDbcType dbcType = makeSureTypeExist(pm.getContainerType(), services);
            if (dbcType != null) {
               if (pm.isConstructor()) {
                  DbcConstructor constructor = DbcmodelFactory.eINSTANCE.createDbcConstructor();
                  if (dbcType instanceof DbcClass) {
                     ((DbcClass) dbcType).getConstructors().add(constructor);
                  }
                  else if (dbcType instanceof DbcEnum) {
                     ((DbcEnum) dbcType).getConstructors().add(constructor);
                  }
                  else {
                     throw new IllegalStateException("Parent \"" + dbcType + "\" is not supposed to contain constructors.");
                  }
                  result = constructor;
               }
               else {
                  DbcMethod method = DbcmodelFactory.eINSTANCE.createDbcMethod();
                  method.setAbstract(pm.isAbstract());
                  method.setFinal(pm.isFinal());
                  if (pm.getMethodDeclaration() != null && pm.getMethodDeclaration().getTypeReference() != null) {
                     String returnType = KeyConnection.getTypeName(pm.getMethodDeclaration().getTypeReference(), DSPackageManagement.NO_PACKAGES);
                     method.setReturnType(returnType);
                  }
                  else {
                     method.setReturnType(KeyConnection.VOID);
                  }
                  if (dbcType instanceof DbcClass) {
                     ((DbcClass) dbcType).getMethods().add(method);
                  }
                  else if (dbcType instanceof DbcEnum) {
                     ((DbcEnum) dbcType).getMethods().add(method);
                  }
                  else if (dbcType instanceof DbcInterface) {
                     ((DbcInterface) dbcType).getMethods().add(method);
                  }
                  else {
                     throw new DSException("Parent \"" + dbcType + "\" is not supposed to contain constructors.");
                  }
                  result = method;
               }
               result.setSignature(KeyConnection.getSignature(pm));
               result.setStatic(pm.isStatic());
               if (pm.isPrivate()) {
                  result.setVisibility(DbcVisibility.PRIVATE);
               }
               else if (pm.isProtected()) {
                  result.setVisibility(DbcVisibility.PROTECTED);
               }
               else if (pm.isPublic()) {
                  result.setVisibility(DbcVisibility.PUBLIC);
               }
               else {
                  result.setVisibility(DbcVisibility.DEFAULT);
               }
               operationMapping.put(pm, result);
            }
         }
         return result;
      }
      else {
         return null;
      }
   }
   
   /**
    * Makes sure that the given {@link KeYJavaType} is part of the {@link DbcModel}.
    * @param kjt The {@link KeYJavaType} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link AbstractDbcType} which represents the given {@link KeYJavaType}.
    * @throws DSException Occurred Exception.
    */
   protected AbstractDbcType makeSureTypeExist(KeYJavaType kjt, Services services) throws DSException {
      if (!KeYTypeUtil.isLibraryClass(kjt)) {
         AbstractDbcType result = typeMapping.get(kjt);
         if (result == null) {
            ClassType ct = (ClassType)kjt.getJavaType();
            if (ct.isInterface()) {
               DbcInterface dbcInterface = DbcmodelFactory.eINSTANCE.createDbcInterface();
               addToParentTypeOrModelOtherwise(dbcInterface, kjt, services);
               result = dbcInterface;
            }
            else if (ct instanceof EnumClassDeclaration) {
               DbcEnum dbcEnum = DbcmodelFactory.eINSTANCE.createDbcEnum();
               addToParentTypeOrModelOtherwise(dbcEnum, kjt, services);
               result = dbcEnum;
            }
            else {
               DbcClass dbcClass = DbcmodelFactory.eINSTANCE.createDbcClass();
               dbcClass.setAbstract(ct.isAbstract());
               dbcClass.setAnonymous(((ClassDeclaration)ct).isAnonymousClass());
               dbcClass.setFinal(ct.isFinal());
               addToParentTypeOrModelOtherwise(dbcClass, kjt, services);
               result = dbcClass;
            }
            result.setName(KeyConnection.getTypeName(kjt, DSPackageManagement.NO_PACKAGES));
            result.setStatic(ct.isStatic());
            if (ct.isPrivate()) {
               result.setVisibility(DbcVisibility.PRIVATE);
            }
            else if (ct.isProtected()) {
               result.setVisibility(DbcVisibility.PROTECTED);
            }
            else if (ct.isPublic()) {
               result.setVisibility(DbcVisibility.PUBLIC);
            }
            else {
               result.setVisibility(DbcVisibility.DEFAULT);
            }
            typeMapping.put(kjt, result);
         }
         return result;
      }
      else {
         return null;
      }
   }
   
   /**
    * Adds the given {@link AbstractDbcType} to its container {@link AbstractDbcType} or
    * directly to the {@link DbcModel} if it is not an inner or anonymous type.
    * @param dbcType The {@link AbstractDbcType} to add to its parent.
    * @param kjt The {@link KeYJavaType} which is represented by the given {@link AbstractDbcType}.
    * @param services The {@link Services} to use.
    * @throws DSException Occurred Exception.
    */
   protected void addToParentTypeOrModelOtherwise(AbstractDbcType dbcType, KeYJavaType kjt, Services services) throws DSException {
      if (KeYTypeUtil.isInnerType(services, kjt)) {
         String parentFullName = KeYTypeUtil.getParentName(services, kjt);
         KeYJavaType parentKjt = KeYTypeUtil.getType(services, parentFullName);
         if (parentKjt == null) {
            throw new DSException("Unable to find parent KeYJavaType for \"" + parentFullName + "\".");
         }
         AbstractDbcType dbcParentType = makeSureTypeExist(parentKjt, services);
         if (dbcParentType == null) {
            throw new DSException("Unable to create parent for \"" + dbcParentType + "\".");
         }
         dbcParentType.getTypes().add(dbcType);
      }
      else {
         dbcModel.getTypes().add(dbcType);
      }
   }

   /**
    * Makes sure that the given {@link IProgramVariable} is part of the {@link DbcModel}.
    * @param pv The {@link IProgramVariable} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link DbcEnumLiteral} which represents the given {@link IProgramVariable}.
    * @throws DSException Occurred Exception.
    */
   protected DbcEnumLiteral makeSureLiteralExist(IProgramVariable pv, Services services) throws DSException {
      if (!(pv instanceof ProgramVariable)) {
         throw new DSException("\"" + pv + "\" is no ProgramVariable.");
      }
      Field field = toField((ProgramVariable)pv, services);
      if (field == null) {
         throw new DSException("Unable to find field of \"" + pv + "\".");
      }
      DbcEnumLiteral result = literalMapping.get(pv);
      if (result == null) {
         AbstractDbcType dbcType = makeSureTypeExist(((ProgramVariable)pv).getContainerType(), services);
         if (dbcType != null) {
            result = DbcmodelFactory.eINSTANCE.createDbcEnumLiteral();
            result.setName(field.getProgramName());
            if (dbcType instanceof DbcEnum) {
               ((DbcEnum) dbcType).getLiterals().add(result);
            }
            else {
               throw new DSException("Parent \"" + dbcType + "\" is not supposed to contain literals.");
            }
            literalMapping.put(pv, result);
         }
      }
      return result;
   }

   /**
    * Makes sure that the given {@link IProgramVariable} is part of the {@link DbcModel}.
    * @param pv The {@link IProgramVariable} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link DbcAttribute} which represents the given {@link IProgramVariable}.
    * @throws DSException Occurred Exception.
    */
   protected DbcAttribute makeSureAttributeExist(IProgramVariable pv, Services services) throws DSException {
      if (!(pv instanceof ProgramVariable)) {
         throw new DSException("\"" + pv + "\" is no ProgramVariable.");
      }
      if (!((ProgramVariable)pv).isImplicit()) {
         DbcAttribute result = attributeMapping.get(pv);
         if (result == null) {
            AbstractDbcType dbcType = makeSureTypeExist(((ProgramVariable)pv).getContainerType(), services);
            if (dbcType != null) {
               Field field = toField((ProgramVariable)pv, services);
               if (field == null) {
                  throw new DSException("Unable to find field of \"" + pv + "\".");
               }
               result = DbcmodelFactory.eINSTANCE.createDbcAttribute();
               result.setFinal(field.isFinal());
               result.setName(field.getProgramName());
               result.setStatic(field.isStatic());
               result.setType(KeyConnection.getTypeName(field.getType(), DSPackageManagement.NO_PACKAGES));
               if (field.isPrivate()) {
                  result.setVisibility(DbcVisibility.PRIVATE);
               }
               else if (field.isProtected()) {
                  result.setVisibility(DbcVisibility.PROTECTED);
               }
               else if (field.isPublic()) {
                  result.setVisibility(DbcVisibility.PUBLIC);
               }
               else {
                  result.setVisibility(DbcVisibility.DEFAULT);
               }
               if (dbcType instanceof DbcClass) {
                  ((DbcClass) dbcType).getAttributes().add(result);
               }
               else if (dbcType instanceof DbcInterface) {
                  ((DbcInterface) dbcType).getAttributes().add(result);
               }
               else if (dbcType instanceof DbcEnum) {
                  ((DbcEnum) dbcType).getAttributes().add(result);
               }
               else {
                  throw new DSException("Parent \"" + dbcType + "\" is not supposed to contain attributes.");
               }
               attributeMapping.put(pv, result);
            }
         }
         return result;
      }
      else {
         return null;
      }
   }

   /**
    * Returns the {@link Field} definition for the given {@link ProgramVariable}.
    * @param pv The {@link ProgramVariable} to search its {@link Field} definition.
    * @param services The {@link Services} to use.
    * @return The found {@link Field} or {@code null} if not available.
    */
   protected Field toField(final ProgramVariable pv, Services services) {
      ClassType ct = (ClassType)pv.getContainerType().getJavaType();
      ImmutableList<Field> fields = ct.getAllFields(services);
      return CollectionUtil.search(fields, new IFilter<Field>() {
         @Override
         public boolean select(Field element) {
            return pv.equals(element.getProgramVariable());
         }
      });
   }

   /**
    * Makes sure that the given {@link ClassAxiom} is part of the {@link DbcModel}.
    * @param ca The {@link ClassAxiom} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link DbcAxiom} which represents the given {@link ClassAxiom}.
    * @throws DSException Occurred Exception.
    */
   protected DbcAxiom makeSureAxiomExist(ClassAxiom ca, Services services) throws DSException {
      if (KeyConnection.shouldIncludeClassAxiom(services, ca.getKJT(), ca)) {
         DbcAxiom result = axiomMapping.get(ca);
         if (result == null) {
            AbstractDbcType dbcType = makeSureTypeExist(ca.getKJT(), services);
            if (dbcType != null) {
               result = DbcmodelFactory.eINSTANCE.createDbcAxiom();
               result.setDefinition(ObjectUtil.toString(ca));
               result.setName(ca.getName());
               dbcType.getAxioms().add(result);
               axiomMapping.put(ca, result);
            }
         }
         return result;
      }
      else {
         return null;
      }
   }

   /**
    * Makes sure that the given {@link ClassInvariant} is part of the {@link DbcModel}.
    * @param ci The {@link ClassInvariant} which should be included in the {@link DbcModel}.
    * @param services The {@link Services} to use.
    * @return The {@link DbcInvariant} which represents the given {@link ClassInvariant}.
    * @throws DSException Occurred Exception.
    */
   protected DbcInvariant makeSureInvariantExist(ClassInvariant ci, Services services) throws DSException {
      DbcInvariant result = invariantMapping.get(ci);
      if (result == null) {
         AbstractDbcType dbcType = makeSureTypeExist(ci.getKJT(), services);
         if (dbcType != null) {
            result = DbcmodelFactory.eINSTANCE.createDbcInvariant();
            result.setCondition(KeyHacks.getClassInvariantText(services, ci));
            result.setName(ci.getName());
            dbcType.getInvariants().add(result);
            invariantMapping.put(ci, result);
         }
      }
      return result;
   }
}