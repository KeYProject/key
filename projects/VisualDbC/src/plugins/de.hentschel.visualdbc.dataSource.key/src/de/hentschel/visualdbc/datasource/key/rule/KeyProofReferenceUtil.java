/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.key.rule;

import java.util.Iterator;
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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.Proof;

/**
 * Provides static methods to extract references from proofs in KeY.
 * @author Martin Hentschel
 * @see IRuleAnalyst
 * @see MethodBodyExpandRuleAnalyst
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
    * The proof step "strictlyPureMethodToUpdate".
    */
   public static final String STRICTLY_PURE_METHOD_TO_UPDATE = "strictlyPureMethodToUpdate";
   
   /**
    * A reference to a guarded invariant.
    */   
   public static final String GUARDED_INVARIANT = "Guarded Invariant";

   /**
    * The proof step "Use Operation Contract".
    */
   public static final String USE_OPERATION_CONTRACT = "Use Operation Contract";

   /**
    * A reference to an assumed invariant.
    */
   public static final String ASSUMED_INVARIANT = "Assumed Invariant";

   /**
    * A reference to an ensured invariant.
    */
   public static final String ENSURED_INVARIANT = "Ensured Invariant";
   
   /**
    * A reference to a guard.
    */   
   public static final String GUARD = "Guard";

   /**
    * A reference to a super type.
    */
   public static final String SUPER_TYPE = "Super Type";

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
    * Used operation contracts are directly extracted from the proof.
    * </p>
    * <p>
    * Used operation calls are extracted by traversing through the proof tree
    * and by analyzing the applied rule on each node.
    * </p>
    * @param connection The {@link KeyConnection} to use.
    * @param services The {@link Services} to use.
    * @param proof The {@link Proof} to analyze.
    * @return The found references that are might be empty if no references were found.
    */
   public static List<IDSProvableReference> analyzeProof(KeyConnection connection, Services services, Proof proof) {
      return analyzeProofTree(connection, services, proof.root());
   }
   
   /**
    * Computes all available proof references by analyzing the complete
    * proof tree recursive. The references of each {@link Node} are computed
    * via {@link #getReferences(KeyConnection, Services, Node)}.
    * @param connection The {@link KeyConnection} to use.
    * @param services The {@link Services} to use.
    * @param node The {@link Node} to analyze.
    * @return The found references that are might be empty if no references were found.
    */
   public static List<IDSProvableReference> analyzeProofTree(KeyConnection connection,
                                                             Services services, 
                                                             Node node) {
      List<IDSProvableReference> result = new LinkedList<IDSProvableReference>();
      result.addAll(getReferences(connection, services, node));
      NodeIterator iter = node.childrenIterator();
      while (iter.hasNext()) {
         result.addAll(analyzeProofTree(connection, services, iter.next()));
      }
      return result;
   }
   
   /**
    * Extracts all references from the given {@link Node}.
    * @param connection The {@link KeyConnection} to use.
    * @param services The {@link Services} to use.
    * @param node The {@link Node} to analyze.
    * @return The found references that are might be empty if no references were found.
    */
   public static List<IDSProvableReference> getReferences(KeyConnection connection,
                                                          Services services, 
                                                          Node node) {
      List<IDSProvableReference> result;
      IRuleAnalyst analyst = getRuleAnalyst(connection, services, node);
      if (analyst != null) {
         result = analyst.getReferences(connection, services, node);
      }
      else {
         result = new LinkedList<IDSProvableReference>();
      }
      return result;
   }
   
   /**
    * Returns the first {@link IRuleAnalyst} in {@link #getRuleAnalysts()}
    * that can handle the given {@link Node}.
    * @param connection The {@link KeyConnection} to use.
    * @param services The {@link Services} to use.
    * @param node The {@link Node} to handle.
    * @return The found {@link IRuleAnalyst} or {@code null} if no one can handle the {@link Node}.
    */
   public static IRuleAnalyst getRuleAnalyst(KeyConnection connection,
                                             Services services, 
                                             Node node) {
      Iterator<IRuleAnalyst> analystsIter = getRuleAnalysts().iterator();
      IRuleAnalyst result = null;
      while (result == null && analystsIter.hasNext()) {
         IRuleAnalyst next = analystsIter.next();
         if (next.canHandle(connection, services, node)) {
            result = next;
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
      // Create result list for each priority
      List<IRuleAnalyst> veryLowAnalysts = new LinkedList<IRuleAnalyst>();
      List<IRuleAnalyst> lowAnalysts = new LinkedList<IRuleAnalyst>();
      List<IRuleAnalyst> normalAnalysts = new LinkedList<IRuleAnalyst>();
      List<IRuleAnalyst> highAnalysts = new LinkedList<IRuleAnalyst>();
      List<IRuleAnalyst> veryHighAnalysts = new LinkedList<IRuleAnalyst>();
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
                     String priority = configElement.getAttribute("priority");
                     if ("VERY_HIGH".equals(priority)) {
                        veryHighAnalysts.add(analyst);
                     }
                     else if ("HIGH".equals(priority)) {
                        highAnalysts.add(analyst);
                     }
                     else if ("NORMAL".equals(priority)) {
                        normalAnalysts.add(analyst);
                     }
                     else if ("LOW".equals(priority)) {
                        lowAnalysts.add(analyst);
                     }
                     else {
                        veryLowAnalysts.add(analyst);
                     }
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
      // Return analysts ordered by their priority
      List<IRuleAnalyst> result = new LinkedList<IRuleAnalyst>();
      result.addAll(veryHighAnalysts);
      result.addAll(highAnalysts);
      result.addAll(normalAnalysts);
      result.addAll(lowAnalysts);
      result.addAll(veryLowAnalysts);
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
