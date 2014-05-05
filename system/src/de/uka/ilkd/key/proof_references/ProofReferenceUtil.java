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

package de.uka.ilkd.key.proof_references;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof_references.analyst.ClassAxiomAndInvariantProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.ContractProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.IProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.MethodBodyExpandProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.MethodCallProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.ProgramVariableReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * <p>
 * This class provides static methods to compute proof references. 
 * A proof reference is a source code member used during proof like
 * methods, instance or class variables or operation contracts.
 * </p>
 * <p>
 * A found proof reference is an instance of {@link IProofReference}.
 * </p>
 * <p>
 * Proof references are computed for each {@link Node} separately based
 * on the applied rule. Instances of {@link IProofReferencesAnalyst} are used
 * to implement the rule specific extraction of such references.
 * </p>
 * <p>
 * This functionality is used by the Eclipse Projects like Visual DbC.
 * </p>
 * @author Martin Hentschel
 * @see IProofReference
 * @see IProofReferencesAnalyst.
 */
public final class ProofReferenceUtil {
   /**
    * The default {@link IProofReferencesAnalyst}s.
    */
   public static final ImmutableList<IProofReferencesAnalyst> DEFAULT_ANALYSTS = ImmutableSLList.<IProofReferencesAnalyst>nil().append(new MethodBodyExpandProofReferencesAnalyst(),
                                                                                                                                       new MethodCallProofReferencesAnalyst(),
                                                                                                                                       new ContractProofReferencesAnalyst(),
                                                                                                                                       new ProgramVariableReferencesAnalyst(),
                                                                                                                                       new ClassAxiomAndInvariantProofReferencesAnalyst());
   
   /**
    * Forbid instances.
    */
   private ProofReferenceUtil() {
   }

   /**
    * <p>
    * Computes all proof references in the given {@link Proof} by
    * iterating over all {@link Node}s in breath first order.
    * </p>
    * <p>
    * Changes during computation of the proof tree are not detected
    * and should be avoided. Otherwise it is possible that the result is wrong.
    * </p>
    * @param proof The {@link Proof} to compute its references.
    * @return The found {@link IProofReference}s.
    */
   public static LinkedHashSet<IProofReference<?>> computeProofReferences(Proof proof) {
      return computeProofReferences(proof, DEFAULT_ANALYSTS);
   }

   /**
    * <p>
    * Computes all proof references in the given {@link Proof} by
    * iterating over all {@link Node}s in breath first order.
    * </p>
    * <p>
    * Changes during computation of the proof tree are not detected
    * and should be avoided. Otherwise it is possible that the result is wrong.
    * </p>
    * @param proof The {@link Proof} to compute its references.
    * @param analysts The {@link IProofReferencesAnalyst} to use.
    * @return The found {@link IProofReference}s.
    */
   public static LinkedHashSet<IProofReference<?>> computeProofReferences(Proof proof, 
                                                                          ImmutableList<IProofReferencesAnalyst> analysts) {
      if (proof != null) {
         Services services = proof.getServices();
         ReferenceAnalaystProofVisitor visitor = new ReferenceAnalaystProofVisitor(services, analysts);
         proof.breadthFirstSearch(proof.root(), visitor);
         return visitor.getResult();
      }
      else {
         return new LinkedHashSet<IProofReference<?>>();
      }
   }
   
   /**
    * Utility class used by {@link KeyProofReferenceUtil#analyzeProof(KeyConnection, Services, Proof)}.
    * @author Martin Hentschel
    */
   private static class ReferenceAnalaystProofVisitor implements ProofVisitor {
      /**
       * The {@link Services} to use.
       */
      private Services services;
      
      /**
       * The {@link IProofReferencesAnalyst}s to use.
       */
      private ImmutableList<IProofReferencesAnalyst> analysts;
      
      /**
       * The result.
       */
      private LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<IProofReference<?>>();

      /**
       * Constructor.
       * @param services The {@link Services} to use.
       * @param analysts The {@link IProofReferencesAnalyst}s to use.
       */
      public ReferenceAnalaystProofVisitor(Services services, ImmutableList<IProofReferencesAnalyst> analysts) {
         this.services = services;
         this.analysts = analysts;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Proof proof, Node visitedNode) {
         merge(result, computeProofReferences(visitedNode, services, analysts));
      }

      /**
       * Returns the result.
       * @return The result.
       */
      public LinkedHashSet<IProofReference<?>> getResult() {
         return result;
      }
   }

   /**
    * Computes the {@link IProofReference} of the given {@link Node}.
    * @param node The {@link Node} to compute its {@link IProofReference}s.
    * @param services The {@link Services} to use.
    * @return The found {@link IProofReference}s.
    */
   public static LinkedHashSet<IProofReference<?>> computeProofReferences(Node node, 
                                                                          Services services) {
      return computeProofReferences(node, services, DEFAULT_ANALYSTS);
   }

   /**
    * Computes the {@link IProofReference} of the given {@link Node}.
    * @param node The {@link Node} to compute its {@link IProofReference}s.
    * @param services The {@link Services} to use.
    * @param analysts The {@link IProofReferencesAnalyst} to use.
    * @return The found {@link IProofReference}s.
    */
   public static LinkedHashSet<IProofReference<?>> computeProofReferences(Node node, 
                                                                          Services services, 
                                                                          ImmutableList<IProofReferencesAnalyst> analysts) {
      LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<IProofReference<?>>();
      if (node != null && analysts != null) {
         for (IProofReferencesAnalyst analyst : analysts) {
            LinkedHashSet<IProofReference<?>> analystResult = analyst.computeReferences(node, services);
            if (analystResult != null) {
               merge(result, analystResult);
            }
         }
      }
      return result;
   }
   
   /**
    * Merges the {@link IProofReference}s to add into the target.
    * @param target The target to add to.
    * @param toAdd The {@link IProofReference}s to add.
    */
   public static void merge(LinkedHashSet<IProofReference<?>> target, LinkedHashSet<IProofReference<?>> toAdd) {
      for (IProofReference<?> reference : toAdd) {
         merge(target, reference);
      }
   }
   
   /**
    * Merges the {@link IProofReference} into the target:
    * @param target The target to add to.
    * @param reference The {@link IProofReference} to add.
    */
   public static void merge(LinkedHashSet<IProofReference<?>> target, final IProofReference<?> reference) {
      if (!target.add(reference)) {
         // Reference exist before, so merge nodes of both references.
         IProofReference<?> existingFirst = JavaUtil.search(target, new IFilter<IProofReference<?>>() {
            @Override
            public boolean select(IProofReference<?> element) {
               return element.equals(reference);
            }
         });
         existingFirst.addNodes(reference.getNodes());
      }
   }
}