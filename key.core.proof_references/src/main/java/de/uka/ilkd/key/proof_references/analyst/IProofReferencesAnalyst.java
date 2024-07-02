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

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * <p>
 * Instances of this class are used to compute {@link IProofReference} for
 * a given {@link Node} based on the applied rule. Each instance of this class
 * has the knowledge to extract the references for a single rule or a group of similar rules.
 * </p>
 * <p>
 * The complete extraction is done via static methods of {@link ProofReferenceUtil}.
 * </p>
 * @author Martin Hentschel
 * @see ProofReferenceUtil
 * @see IProofReference
 */
public interface IProofReferencesAnalyst {
   /**
    * Computes the {@link IProofReference} for the given {@link Node} which
    * can be {@code null} or an empty set if the applied rule is not supported by this {@link IProofReferencesAnalyst}.
    * @param node The {@link Node} to compute its {@link IProofReference}s.
    * @param services The {@link Services} to use.
    * @return The found {@link IProofReference} or {@code null}/empty set if the applied rule is not supported.
    */
   public LinkedHashSet<IProofReference<?>> computeReferences(Node node, Services services);
}