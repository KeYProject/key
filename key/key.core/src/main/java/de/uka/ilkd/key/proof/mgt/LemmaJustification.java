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

package de.uka.ilkd.key.proof.mgt;

/**
 * {@link RuleJustification} for taclets, that can be proven from other taclets.
 */
public class LemmaJustification implements RuleJustification {

   public static final LemmaJustification INSTANCE = new LemmaJustification();

   private LemmaJustification() {
   }

   @Override
   public boolean isAxiomJustification() {
      return false;
   }
}
