// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil.ContractPostOrExcPostExceptionVariableResult;

/**
 * The default implementation of {@link IExecutionOperationContract}.
 * @author Martin Hentschel
 */
public class ExecutionOperationContract extends AbstractExecutionNode<SourceElement> implements IExecutionOperationContract {
   /**
    * The exception {@link Term} used by the applied {@link Contract}.
    */
   private Term exceptionTerm;

   /**
    * The result {@link Term} used by the applied {@link Contract}.
    */
   private Term resultTerm;

   /**
    * The self {@link Term} or {@code null} if not available.
    */
   private Term selfTerm;
   
   /**
    * The current contract parameters.
    */
   private ImmutableList<Term> contractParams;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionOperationContract(ITreeSettings settings, 
                                     KeYMediator mediator, 
                                     Node proofNode) {
      super(settings, mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      if (!isDisposed()) {
         final Services services = getServices();
         // Make sure that the contract is compatible
         if (!(getContract() instanceof FunctionalOperationContract)) {
            throw new ProofInputException("Unsupported contract: " + getContract());
         }
         FunctionalOperationContract contract = (FunctionalOperationContract)getContract();
         // Compute instantiation
         Instantiation inst = UseOperationContractRule.computeInstantiation(getProofNode().getAppliedRuleApp().posInOccurrence().subTerm(), services);
         // Extract used result and exception variable from proof nodes
         resultTerm = searchResultTerm(contract, inst, services);
         ContractPostOrExcPostExceptionVariableResult search = SymbolicExecutionUtil.searchContractPostOrExcPostExceptionVariable(getProofNode().child(0), services); // Post branch
         exceptionTerm = search.getExceptionEquality().sub(0);
         // Rename variables in contract to the current one
         List<LocationVariable> heapContext = HeapContext.getModHeaps(services, inst.transaction);
         Map<LocationVariable,LocationVariable> atPreVars = UseOperationContractRule.computeAtPreVars(heapContext, services, inst);
         Map<LocationVariable,Term> atPres = HeapContext.getAtPres(atPreVars, services);
         LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
         Term baseHeapTerm = services.getTermBuilder().getBaseHeap();
         if (contract.hasSelfVar()) {
            if (inst.pm.isConstructor()) {
               selfTerm = searchConstructorSelfDefinition(search.getWorkingTerm(), inst.staticType, services);
               if (selfTerm == null) {
                  throw new ProofInputException("Can't find self term, implementation of UseOperationContractRule might has changed!"); 
               }
               KeYJavaType selfType = services.getJavaInfo().getKeYJavaType(selfTerm.sort());
               if (inst.staticType != selfType) {
                  throw new ProofInputException("Type \"" + inst.staticType + "\" expected but found \"" + selfType + "\", implementation of UseOperationContractRule might has changed!"); 
               }
            }
            else {
               selfTerm = UseOperationContractRule.computeSelf(baseHeapTerm, atPres, baseHeap, inst, resultTerm, services.getTermFactory());
            }
         }
         contractParams = UseOperationContractRule.computeParams(baseHeapTerm, atPres, baseHeap, inst, services.getTermFactory());
         // Compute contract text
         return FunctionalOperationContractImpl.getText(contract, 
                                                        contractParams, 
                                                        resultTerm, 
                                                        selfTerm, 
                                                        exceptionTerm, 
                                                        baseHeap, 
                                                        baseHeapTerm, 
                                                        heapContext, 
                                                        atPres, 
                                                        false, 
                                                        services,
                                                        getSettings().isUsePrettyPrinting(),
                                                        getSettings().isUseUnicode()).trim();
      }
      else {
         return null;
      }
   }
   
   /**
    * Tries to find the self {@link Term} of the given {@link KeYJavaType}.
    * @param term The {@link Term} to start search in.
    * @param staticType The expected {@link KeYJavaType}.
    * @param services The {@link Services} to use.
    * @return The found self {@link Term} or {@code null} if not available.
    */
   protected Term searchConstructorSelfDefinition(Term term, KeYJavaType staticType, Services services) {
      if (term.op() == Junctor.NOT &&
          term.sub(0).op() == Equality.EQUALS && 
          term.sub(0).sub(0).op() instanceof LocationVariable && 
          SymbolicExecutionUtil.isNullSort(term.sub(0).sub(1).sort(), services) &&
          services.getJavaInfo().getKeYJavaType(term.sub(0).sub(0).sort()) == staticType) {
         return term.sub(0).sub(0);
      }
      else {
         Term result = null;
         int i = term.arity() - 1;
         while (result == null && i >= 0) {
            result = searchConstructorSelfDefinition(term.sub(i), staticType, services);
            i--;
         }
         return result;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Term getResultTerm() throws ProofInputException {
      synchronized (this) {
         if (!isNameComputed()) {
            getName(); // Compute name and result term
         }
         return resultTerm;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Term getExceptionTerm() throws ProofInputException {
      synchronized (this) {
         if (!isNameComputed()) {
            getName(); // Compute name and exception term
         }
         return exceptionTerm;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Term getSelfTerm() throws ProofInputException {
      synchronized (this) {
         if (!isNameComputed()) {
            getName(); // Compute name and self term
         }
         return selfTerm;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Term> getContractParams() throws ProofInputException {
      synchronized (this) {
         if (!isNameComputed()) {
            getName(); // Compute name and contract term
         }
         return contractParams;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedResultTerm() throws ProofInputException {
      Term resultTerm = getResultTerm();            
      return resultTerm != null ? formatTerm(resultTerm, getServices()) : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedExceptionTerm() throws ProofInputException {
      Term exceptionTerm = getExceptionTerm();
      return exceptionTerm != null ? formatTerm(exceptionTerm, getServices()) : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedSelfTerm() throws ProofInputException {
      Term selfTerm = getSelfTerm();
      return selfTerm != null ? formatTerm(selfTerm, getServices()) : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedContractParams() throws ProofInputException {
      ImmutableList<Term> contractParams = getContractParams();
      if (contractParams != null && !contractParams.isEmpty()) {
         StringBuffer sb = new StringBuffer();
         boolean afterFirst = false;
         for (Term term : contractParams) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            sb.append(formatTerm(term, getServices()));
         }
         return sb.toString();
      }
      else {
         return null;
      }
   }
   
   /**
    * Searches the result {@link Term}.
    * @param contract The {@link FunctionalOperationContract}.
    * @param inst The {@link Instantiation}.
    * @param services The {@link Services}.
    * @return The found result {@link Term} or {@code null} otherwise.
    */
   protected Term searchResultTerm(FunctionalOperationContract contract, Instantiation inst, Services services) {
      Term resultTerm = null;
      if (contract.hasResultVar()) {
         ProgramVariable resultVar = extractResultVariableFromPostBranch(getProofNode(), services);
         if (resultVar == null) {
            // Result variable not found in child, create a temporary variable to use in specification
            resultVar = UseOperationContractRule.computeResultVar(inst, services);
         }
         resultTerm = services.getTermBuilder().var(resultVar);
      }
      return resultTerm;
   }
   
   /**
    * Extracts the result variable from the given post branch.
    * @param node The {@link Node} which is the post or exceptional post branch of an applied {@link ContractRuleApp}.
    * @param services The {@link Services} to use.
    * @return The found {@link LocationVariable} or {@code null} if not found.
    */
   protected static LocationVariable extractResultVariableFromPostBranch(Node node, Services services) {
      Term postModality = SymbolicExecutionUtil.posInOccurrenceInOtherNode(node, node.getAppliedRuleApp().posInOccurrence(), node.child(0));
      postModality = TermBuilder.goBelowUpdates(postModality);
      MethodFrame mf = JavaTools.getInnermostMethodFrame(postModality.javaBlock(), services);
      SourceElement firstElement = NodeInfo.computeActiveStatement(mf.getFirstElement());
      if (!(firstElement instanceof CopyAssignment)) {
         return null;
      }
      CopyAssignment assignment = (CopyAssignment)firstElement;
      ProgramElement rightChild = assignment.getChildAt(1);
      if (!(rightChild instanceof LocationVariable)) {
         return null;
      }
      return (LocationVariable)rightChild;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Contract getContract() {
      return ((AbstractContractRuleApp)getProofNode().getAppliedRuleApp()).getInstantiation();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramMethod getContractProgramMethod() {
      Contract contract = getContract();
      if (contract instanceof OperationContract) {
         return ((OperationContract)contract).getTarget();
      }
      else {
         return null;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Operation Contract";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IExecutionVariable[] lazyComputeVariables() {
      return SymbolicExecutionUtil.createExecutionVariables(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IExecutionConstraint[] lazyComputeConstraints() {
      return SymbolicExecutionUtil.createExecutionConstraints(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isPreconditionComplied() {
      boolean complied = false;
      if (getProofNode().childrenCount() >= 3) {
         complied = getProofNode().child(2).isClosed();
      }
      return complied;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasNotNullCheck() {
      return getProofNode().childrenCount() >= 4;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isNotNullCheckComplied() {
      if (hasNotNullCheck()) {
         return getProofNode().child(3).isClosed();
      }
      else {
         return false;
      }
   }
}