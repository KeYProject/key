package de.uka.ilkd.key.proof_references;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof_references.analyst.ContractProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.IProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.MethodBodyExpandProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.MethodCallProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

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
                                                                                                                                       new ContractProofReferencesAnalyst());
   
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
   public static ImmutableList<IProofReference<?>> computeProofReferences(Proof proof) {
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
   public static ImmutableList<IProofReference<?>> computeProofReferences(Proof proof, 
                                                                          ImmutableList<IProofReferencesAnalyst> analysts) {
      if (proof != null) {
         Services services = proof.getServices();
         ReferenceAnalaystProofVisitor visitor = new ReferenceAnalaystProofVisitor(services, analysts);
         proof.breadthFirstSearch(proof.root(), visitor);
         return visitor.getResult();
      }
      else {
         return ImmutableSLList.nil();
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
      private ImmutableList<IProofReference<?>> result = ImmutableSLList.nil();

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
         result = result.append(computeProofReferences(visitedNode, services, analysts));
      }

      /**
       * Returns the result.
       * @return The result.
       */
      public ImmutableList<IProofReference<?>> getResult() {
         return result;
      }
   }

   /**
    * Computes the {@link IProofReference} of the given {@link Node}.
    * @param node The {@link Node} to compute its {@link IProofReference}s.
    * @param services The {@link Services} to use.
    * @return The found {@link IProofReference}s.
    */
   public static ImmutableList<IProofReference<?>> computeProofReferences(Node node, 
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
   public static ImmutableList<IProofReference<?>> computeProofReferences(Node node, 
                                                                          Services services, 
                                                                          ImmutableList<IProofReferencesAnalyst> analysts) {
      ImmutableList<IProofReference<?>> result = ImmutableSLList.nil();
      if (node != null && analysts != null) {
         for (IProofReferencesAnalyst analyst : analysts) {
            ImmutableList<IProofReference<?>> analystResult = analyst.computeReferences(node, services);
            if (analystResult != null) {
               result = result.append(analystResult);
            }
         }
      }
      return result;
   }
}
