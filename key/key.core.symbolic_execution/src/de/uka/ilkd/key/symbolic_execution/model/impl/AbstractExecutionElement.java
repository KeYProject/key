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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
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
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionElement(ITreeSettings settings, 
                                   Node proofNode) {
      assert settings != null;
      assert proofNode != null;
      this.settings = settings;
      this.proofNode = proofNode;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Services getServices() {
      Proof proof = getProof();
      return proof != null && !proof.isDisposed() ? proof.getServices() : null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public RuleApp getAppliedRuleApp() {
      return proofNode.getAppliedRuleApp();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public InitConfig getInitConfig() {
      Proof proof = getProof();
      return proof != null && !proof.isDisposed() ? proof.getInitConfig() : null;
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
    * Sets the name.
    * @param name The new name to set.
    */
   protected void setName(String name) {
      this.name = name;
   }
   
   /**
    * Checks if the value of {@link #getName()} is already computed.
    * @return {@code ture} name is computed, {@code false} name is not computed yet.
    */
   protected boolean isNameComputed() {
      return name != null;
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
    * @param services The {@link Services} to use.
    * @return The {@link String} representation of the given {@link Term}.
    */
   protected String formatTerm(Term term, Services services) {
      return SymbolicExecutionUtil.formatTerm(term, 
                                              services, 
                                              settings.isUseUnicode(),
                                              settings.isUsePrettyPrinting());
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