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

package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionOperationContract;

/**
 * <p>
 * A node in the symbolic execution tree which represents a use operation contract application.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionOperationContract} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionOperationContract
 */
public interface IExecutionOperationContract extends IExecutionNode<SourceElement> {
   /**
    * Returns the applied {@link Contract}.
    * @return The applied {@link Contract}.
    */
   public Contract getContract();
   
   /**
    * Returns the {@link IProgramMethod} of the applied {@link Contract}.
    * @return The {@link IProgramMethod} of the applied {@link Contract}.
    */
   public IProgramMethod getContractProgramMethod();
   
   /**
    * Checks if the precondition is complied.
    * @return {@code true} precondition complied, {@code false} precondition not complied.
    */
   public boolean isPreconditionComplied(); 

   /**
    * Checks if a not null check is available (instance method) or not (static method or constructor).
    * @return {@code true} not null check available, {@code false} not null check is not available.
    */
   public boolean hasNotNullCheck();
   
   /**
    * Checks if the not null check is complied.
    * @return {@code true} not null check complied, {@code false} not null check not complied.
    */
   public boolean isNotNullCheckComplied();
   
   /**
    * Returns the result {@link Term} in which the result of the applied {@link Contract} is stored.
    * @return The result {@link Term} in which the result of the applied {@link Contract} is stored.
    * @throws ProofInputException Occurred Exception.
    */
   public Term getResultTerm() throws ProofInputException;
   
   /**
    * Returns the exception {@link Term} in which a by the {@link Contract} thrown {@link Exception} is stored.
    * @return The exception {@link Term} in which a by the {@link Contract} thrown {@link Exception} is stored.
    * @throws ProofInputException Occurred Exception.
    */
   public Term getExceptionTerm() throws ProofInputException;
   
   /**
    * Returns the self {@link Term} of the called method for which a {@link Contract} is applied.
    * @return The self {@link Term} or {@code null} if not available.
    * @throws ProofInputException Occurred Exception.
    */
   public Term getSelfTerm() throws ProofInputException;
   
   /**
    * Returns the parameters of the called method for which a {@link Contract} is applied.
    * @return The parameters of the called method for which a {@link Contract} is applied.
    * @throws ProofInputException Occurred Exception.
    */
   public ImmutableList<Term> getContractParams() throws ProofInputException;
   
   /**
    * Returns the human readable result {@link Term} in which the result of the applied {@link Contract} is stored.
    * @return The human readable result {@link Term} in which the result of the applied {@link Contract} is stored.
    * @throws ProofInputException Occurred Exception.
    */
   public String getFormatedResultTerm() throws ProofInputException;
   
   /**
    * Returns the human readable exception {@link Term} in which a by the {@link Contract} thrown {@link Exception} is stored.
    * @return The human readable exception {@link Term} in which a by the {@link Contract} thrown {@link Exception} is stored.
    * @throws ProofInputException Occurred Exception.
    */
   public String getFormatedExceptionTerm() throws ProofInputException;
   
   /**
    * Returns the human readable self {@link Term} of the called method for which a {@link Contract} is applied.
    * @return The human readable self {@link Term} or {@code null} if not available.
    * @throws ProofInputException Occurred Exception.
    */
   public String getFormatedSelfTerm() throws ProofInputException;
   
   /**
    * Returns the human readable parameters of the called method for which a {@link Contract} is applied.
    * @return The human readable parameters of the called method for which a {@link Contract} is applied.
    * @throws ProofInputException Occurred Exception.
    */
   public String getFormatedContractParams() throws ProofInputException;
}