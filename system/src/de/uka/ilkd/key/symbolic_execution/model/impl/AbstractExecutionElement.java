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

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides a basic implementation of {@link IExecutionElement}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionElement implements IExecutionElement {
   /**
    * The used {@link TreeSettings}.
    */
   private final ITreeSettings settings;
   
   /**
    * The used {@link KeYMediator} during proof.
    */
   private final KeYMediator mediator;

   /**
    * The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   private final Node proofNode;
   
   /**
    * The human readable name of this node.
    */
   private String name;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionElement(ITreeSettings settings, 
                                   KeYMediator mediator, 
                                   Node proofNode) {
      assert settings != null;
      assert mediator != null;
      assert proofNode != null;
      this.settings = settings;
      this.mediator = mediator;
      this.proofNode = proofNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYMediator getMediator() {
      return mediator;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Services getServices() {
      return getProof().getServices();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getProof() {
      return getProofNode().proof();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Node getProofNode() {
      return proofNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public NodeInfo getProofNodeInfo() {
      return getProofNode().getNodeInfo();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws ProofInputException {
      synchronized (this) {
         if (name == null) {
            name = lazyComputeName();
         }
         return name;
      }
   }

   /**
    * Computes the name of this node lazily when {@link #getName()}
    * is called the first time.
    * @return The human readable name of this {@link IExecutionNode}.
    */
   protected abstract String lazyComputeName() throws ProofInputException;
   
   /**
    * Converts the given {@link Term} into a {@link String} respecting {@link #isUsePretty()}.
    * @param term The {@link Term} to convert.
    * @return The {@link String} representation of the given {@link Term}.
    */
   protected String formatTerm(Term term) {
      return SymbolicExecutionUtil.formatTerm(term, getServices(), settings.isUsePrettyPrinting());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      try {
         return getElementType() + " " + getName();
      }
      catch (ProofInputException e) {
         return getElementType() + " " + e.getMessage();
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDisposed() {
      return getProof().isDisposed();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ITreeSettings getSettings() {
      return settings;
   }
}