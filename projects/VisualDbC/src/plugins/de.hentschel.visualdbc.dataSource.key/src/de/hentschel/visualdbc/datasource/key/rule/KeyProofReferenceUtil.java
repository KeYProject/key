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

package de.hentschel.visualdbc.datasource.key.rule;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.util.LogUtil;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;

/**
 * Provides static methods to extract references from proofs in KeY.
 * @author Martin Hentschel
 * @see IRuleAnalyst
 * @see DefaultRuleAnalyst
 * @see StrictlyPureMethodToUpdateRuleAnalyst
 * @see UseOperationContractRuleAnalyst
 */
public final class KeyProofReferenceUtil {
   /**
    * The extension point for rule analysts.
    */
   public static final String RULE_ANALYST_EXTENSION_POINT = "de.hentschel.visualdbc.dataSource.key.ruleAnalysts";
   
   /**
    * The proof step "methodBodyExpand" that inlines methods.
    */
   public static final String METHOD_BODY_EXPAND = "methodBodyExpand";

   /**
    * The proof step "Use Operation Contract".
    */
   public static final String USE_OPERATION_CONTRACT = "Use Operation Contract";

   /**
    * Contains the available {@link IRuleAnalyst} ordered by their priority.
    */
   private static List<IRuleAnalyst> ruleAnalysts = null;
   
   /**
    * Forbid instances.
    */
   private KeyProofReferenceUtil() {
   }
   
   /**
    * <p>
    * Computes all available proof references.
    * </p>
    * <p>
    * Used operation calls are extracted by traversing through the proof tree
    * and by analyzing the applied rule on each node via available {@link IRuleAnalyst}s.
    * </p>
    * @param connection The {@link KeyConnection} to use.
    * @param services The {@link Services} to use.
    * @param proof The {@link Proof} to analyze.
    * @return The found references that are might be empty if no references were found.
    */
   public static ImmutableList<IDSProvableReference> analyzeProof(KeyConnection connection, 
                                                                  Services services, 
                                                                  Proof proof) {
      ReferenceAnalaystProofVisitor visitor = new ReferenceAnalaystProofVisitor(connection, services);
      proof.breadthFirstSearch(proof.root(), visitor);
      return visitor.getResult();
   }
   
   /**
    * Utility class used by {@link KeyProofReferenceUtil#analyzeProof(KeyConnection, Services, Proof)}.
    * @author Martin Hentschel
    */
   private static class ReferenceAnalaystProofVisitor implements ProofVisitor {
      /**
       * The {@link KeyConnection} to use.
       */
      private KeyConnection connection;
      
      /**
       * The {@link Services} to use.
       */
      private Services services;
      
      /**
       * The result.
       */
      private ImmutableList<IDSProvableReference> result = ImmutableSLList.nil();

      /**
       * Constructor.
       * @param connection The {@link KeyConnection} to use.
       * @param services The {@link Services} to use.
       */
      public ReferenceAnalaystProofVisitor(KeyConnection connection, Services services) {
         this.connection = connection;
         this.services = services;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Proof proof, Node visitedNode) {
         try {
            result = result.append(getReferences(connection, services, visitedNode));
         }
         catch (DSException e) {
            LogUtil.getLogger().logError(e);
         }
      }

      /**
       * Returns the result.
       * @return The result.
       */
      public ImmutableList<IDSProvableReference> getResult() {
         return result;
      }
   }
   
   /**
    * Extracts all references from the given {@link Node}.
    * @param connection The {@link KeyConnection} to use.
    * @param services The {@link Services} to use.
    * @param node The {@link Node} to analyze.
    * @return The found references that are might be empty if no references were found.
    * @throws DSException Occurred Exception.
    */
   public static ImmutableList<IDSProvableReference> getReferences(KeyConnection connection,
                                                                   Services services, 
                                                                   Node node) throws DSException {
      ImmutableList<IDSProvableReference> result = ImmutableSLList.nil();
      for (IRuleAnalyst analyst : getRuleAnalysts()) {
         ImmutableList<IDSProvableReference> analystResult = analyst.getReferences(connection, services, node);
         if (analystResult != null) {
            result = result.append(analystResult);
         }
      }
      return result;
   }
   
   /**
    * Reads all available {@link IRuleAnalyst} from the extension point
    * and creates the instances.
    * @return The created {@link IRuleAnalyst} instances.
    */
   private static List<IRuleAnalyst> createRuleAnalysts() {
      List<IRuleAnalyst> result = new LinkedList<IRuleAnalyst>();
      // Add factories registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(RULE_ANALYST_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     IRuleAnalyst analyst = (IRuleAnalyst)configElement.createExecutableExtension("class");
                     result.add(analyst);
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + RULE_ANALYST_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return result;
   }
   
   /**
    * Returns all available {@link IRuleAnalyst}s ordered by their priority.
    * @return The {@link List} with the available {@link IRuleAnalyst}s.
    */
   public static List<IRuleAnalyst> getRuleAnalysts() {
      // Lazy loading if needed
      if (ruleAnalysts == null) {
         ruleAnalysts = createRuleAnalysts();
      }
      return ruleAnalysts;
   }
}