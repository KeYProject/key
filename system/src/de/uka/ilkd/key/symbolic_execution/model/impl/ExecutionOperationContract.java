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
import de.uka.ilkd.key.pp.NotationInfo;
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
public class ExecutionOperationContract extends AbstractExecutionStateNode<SourceElement> implements IExecutionOperationContract {
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
         ProgramVariable resultVar = null;
         Term resultTerm = null;
         if (contract.hasResultVar()) {
            resultVar = extractResultVariableFromPostBranch(getProofNode(), services);
            if (resultVar == null) {
               // Result variable not found in child, create a temporary variable to use in specification
               resultVar = UseOperationContractRule.computeResultVar(inst, services);
            }
            resultTerm = services.getTermBuilder().var(resultVar);
         }
         ContractPostOrExcPostExceptionVariableResult search = SymbolicExecutionUtil.searchContractPostOrExcPostExceptionVariable(getProofNode().child(0), services); // Post branch
         // Rename variables in contract to the current one
         List<LocationVariable> heapContext = HeapContext.getModHeaps(services, inst.transaction);
         Map<LocationVariable,LocationVariable> atPreVars = UseOperationContractRule.computeAtPreVars(heapContext, services, inst);
         Map<LocationVariable,Term> atPres = HeapContext.getAtPres(atPreVars, services);
         LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
         Term baseHeapTerm = services.getTermBuilder().getBaseHeap();
         
         Term contractSelf = null;
         if (contract.hasSelfVar()) {
            if (inst.pm.isConstructor()) {
               Term selfDefinition = search.getExceptionDefinitionParent();
               selfDefinition = selfDefinition.sub(1);
               while (selfDefinition.op() == Junctor.AND) {
                  selfDefinition = selfDefinition.sub(0);
               }
               // Make sure that self equality was found
               Term selfEquality;
               if (selfDefinition.op() == Junctor.NOT) {
                  selfEquality = selfDefinition.sub(0);
               }
               else {
                  selfEquality = selfDefinition;
               }
               if (selfEquality.op() != Equality.EQUALS || selfEquality.arity() != 2) {
                  throw new ProofInputException("Equality expected, implementation of UseOperationContractRule might has changed!"); 
               }
               if (!SymbolicExecutionUtil.isNullSort(selfEquality.sub(1).sort(), services)) {
                  throw new ProofInputException("Null expected, implementation of UseOperationContractRule might has changed!"); 
               }
               contractSelf = selfEquality.sub(0);
               KeYJavaType selfType = services.getJavaInfo().getKeYJavaType(contractSelf.sort());
               if (inst.staticType != selfType) {
                  throw new ProofInputException("Type \"" + inst.staticType + "\" expected but found \"" + selfType + "\", implementation of UseOperationContractRule might has changed!"); 
               }
            }
            else {
               contractSelf = UseOperationContractRule.computeSelf(baseHeapTerm, atPres, baseHeap, inst, resultTerm, services.getTermFactory());
            }
         }
         ImmutableList<Term> contractParams = UseOperationContractRule.computeParams(baseHeapTerm, atPres, baseHeap, inst, services.getTermFactory());
         // Compute contract text
         synchronized (NotationInfo.class) {
            boolean originalPrettySyntax = NotationInfo.PRETTY_SYNTAX;
            try {
               NotationInfo.PRETTY_SYNTAX = true;
               return FunctionalOperationContractImpl.getText(contract, 
                                                              contractParams, 
                                                              resultTerm, 
                                                              contractSelf, 
                                                              search.getExceptionEquality().sub(0), 
                                                              baseHeap, 
                                                              baseHeapTerm, 
                                                              heapContext, 
                                                              atPres, 
                                                              false, 
                                                              services).trim();
            }
            finally {
               NotationInfo.PRETTY_SYNTAX = originalPrettySyntax;
            }
         }
      }
      else {
         return null;
      }
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