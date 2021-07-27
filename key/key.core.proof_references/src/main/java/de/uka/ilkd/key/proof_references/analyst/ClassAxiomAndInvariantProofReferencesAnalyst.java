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

package de.uka.ilkd.key.proof_references.analyst;

import java.util.Iterator;
import java.util.LinkedHashSet;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof_references.reference.DefaultProofReference;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.PartialInvAxiom;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * Extracts used {@link ClassAxiom} and {@link ClassInvariant}s.
 * @author Martin Hentschel
 */
public class ClassAxiomAndInvariantProofReferencesAnalyst implements IProofReferencesAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public LinkedHashSet<IProofReference<?>> computeReferences(Node node, Services services) {
      String name = MiscTools.getRuleName(node);
      if (name != null && 
          (name.toLowerCase().contains("axiom_for") || name.toLowerCase().contains("represents_clause_for")) && 
          node.getAppliedRuleApp() instanceof PosTacletApp) {
         // Get KeYJavaType which provides the proof obligation because only for its ClassAxioms are taclets generated and used during proof.
         KeYJavaType proofKjt = findProofsKeYJavaType(services);
         if (proofKjt != null) {
            // Get applied taclet name
            Name tacletName = ((PosTacletApp)node.getAppliedRuleApp()).taclet().name();
            // Search ClassAxiom which provides the applied taclet
            ImmutableSet<ClassAxiom> axioms = services.getSpecificationRepository().getClassAxioms(proofKjt);
            ClassAxiom found = null;
            Iterator<ClassAxiom> axiomsIterator = axioms.iterator();
            while (found == null && axiomsIterator.hasNext()) {
               ClassAxiom ca = axiomsIterator.next();
               ImmutableSet<Pair<Sort, IObserverFunction>> toLimit = DefaultImmutableSet.nil();
               ImmutableSet<Taclet> taclets = ca.getTaclets(toLimit, services);
               Iterator<Taclet> tacletIterator = taclets.iterator();
               while (found == null && tacletIterator.hasNext()) {
                  Taclet t = tacletIterator.next();
                  if (t.name().equals(tacletName)) {
                     found = ca;
                  }
               }
            }
            if (found instanceof PartialInvAxiom) {
               // Invariant was applied
               PartialInvAxiom axiom = (PartialInvAxiom)found;
               DefaultProofReference<ClassInvariant> reference = new DefaultProofReference<ClassInvariant>(IProofReference.USE_INVARIANT, node, axiom.getInv());
               LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<IProofReference<?>>();
               result.add(reference);
               return result;
            }
            else if (found != null) {
               // ClassAxiom was applied
               DefaultProofReference<ClassAxiom> reference = new DefaultProofReference<ClassAxiom>(IProofReference.USE_AXIOM, node, found);
               LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<IProofReference<?>>();
               result.add(reference);
               return result;
            }
            else {
               throw new IllegalStateException("ClassAxiom for taclet \"" + name + "\" was not found applied in node \"" + node.serialNr() + "\".");
            }
         }
         else {
            return null; // Proof might be disposed.
         }
      }
      else {
         return null;
      }
   }

   /**
    * Returns the {@link KeYJavaType} which provides the proof obligation of the current proof.
    * @param services The {@link Services} to use.
    * @return The {@link KeYJavaType} which provides the proof obligation or {@code null} if it was not possible to compute it. 
    */
   protected KeYJavaType findProofsKeYJavaType(Services services) {
      ProofOblInput problem = services.getSpecificationRepository().getProofOblInput(services.getProof());
      if (problem != null) {
         KeYJavaType type = problem.getContainerType();
         if (type == null) {
            throw new IllegalStateException("Problem \"" + problem + "\" is not supported.");
         }
         return type;
      }
      else {
         return null; // Proof might be disposed.
      }
   }
}