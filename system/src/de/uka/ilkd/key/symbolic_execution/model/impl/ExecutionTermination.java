// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.util.Pair;

/**
 * The default implementation of {@link IExecutionTermination}.
 * @author Martin Hentschel
 */
public class ExecutionTermination extends AbstractExecutionNode implements IExecutionTermination {
   /**
    * Contains the exception variable which is used to check if the executed program in proof terminates normally.
    */
   private IProgramVariable exceptionVariable;
   
   /**
    * The {@link Sort} of the uncaught exception.
    */
   private Sort exceptionSort;
   
   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param exceptionVariable Contains the exception variable which is used to check if the executed program in proof terminates normally.
    */
   public ExecutionTermination(KeYMediator mediator, Node proofNode, IProgramVariable exceptionVariable) {
      super(mediator, proofNode);
      this.exceptionVariable = exceptionVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return isExceptionalTermination() ? 
             INTERNAL_NODE_NAME_START + "uncaught " + exceptionSort + INTERNAL_NODE_NAME_END : 
             DEFAULT_TERMINATION_NODE_NAME;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramVariable getExceptionVariable() {
      return exceptionVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isExceptionalTermination() {
      Sort sort = getExceptionSort();
      return sort != null && !(sort instanceof NullSort);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Sort getExceptionSort() {
      if (exceptionSort == null) {
         exceptionSort = lazyComputeExceptionSort();
      }
      return exceptionSort;
   }
   
   /**
    * Computes the exception {@link Sort} lazily when {@link #getExceptionSort()}
    * is called the first time. 
    * @return The exception {@link Sort}.
    */
   protected Sort lazyComputeExceptionSort() {
      Sort result = null;
      if (exceptionVariable != null) {
         // Search final value of the exceptional variable which is used to check if the verified program terminates normally
         ImmutableArray<Term> value = null;
         for (SequentFormula f : getProofNode().sequent().succedent()) {
            Pair<ImmutableList<Term>,Term> updates = TermBuilder.DF.goBelowUpdates2(f.formula());
            Iterator<Term> iter = updates.first.iterator();
            while (value == null && iter.hasNext()) {
               value = extractValueFromUpdate(iter.next(), exceptionVariable);
            }
         }
         // An exceptional termination is found if the exceptional variable is not null
         if (value != null && value.size() == 1) {
            result = value.get(0).sort();
         }
      }
      return result;
   }
   
   /**
    * Utility method to extract the value of the {@link IProgramVariable}
    * from the given update term.
    * @param term The given update term.
    * @param variable The {@link IProgramVariable} for that the value is needed.
    * @return The found value or {@code null} if it is not defined in the given update term.
    */
   protected ImmutableArray<Term> extractValueFromUpdate(Term term,
                                                         IProgramVariable variable) {
      ImmutableArray<Term> result = null;
      if (term.op() instanceof ElementaryUpdate) {
         ElementaryUpdate update = (ElementaryUpdate)term.op();;
         if (JavaUtil.equals(variable, update.lhs())) {
            result = term.subs();
         }
      }
      else if (term.op() instanceof UpdateJunctor) {
         Iterator<Term> iter = term.subs().iterator();
         while (result == null && iter.hasNext()) {
            result = extractValueFromUpdate(iter.next(), variable);
         }
      }
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return isExceptionalTermination() ? "Exceptional Termination" : "Termination";
   }
}