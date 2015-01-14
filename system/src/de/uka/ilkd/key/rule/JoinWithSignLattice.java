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

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.abstraction.boollattice.BooleanLattice;
import de.uka.ilkd.key.abstraction.signanalysis.SignAnalysisLattice;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rule that joins two sequents based on a sign lattice
 * for integers. Boolean variables are joined with a simple
 * lattice for booleans. Program variables of other types
 * than int and boolean are unchanged if they are equal in
 * both states and set to fresh variables if they have different
 * values.
 * 
 * TODO: Could also add a null / non-null lattice for objects.
 * 
 * @author Dominic Scheurer
 */
public class JoinWithSignLattice extends JoinWithLatticeAbstraction {
   
   public static final JoinWithSignLattice INSTANCE = new JoinWithSignLattice();
   private static final String DISPLAY_NAME = "JoinBySignLatticeAbstraction";
   private static final Name RULE_NAME = new Name(DISPLAY_NAME);

   @Override
   protected AbstractDomainLattice<?> getAbstractDomainForSort(Sort s, Services services) {
      final Sort intSort =
            (Sort) services.getNamespaces().sorts().lookup(new Name("int"));
      final Sort booleanSort =
            (Sort) services.getNamespaces().sorts().lookup(new Name("boolean"));
      
      if (s.equals(intSort)) {
         return SignAnalysisLattice.getInstance();
      } else if (s.equals(booleanSort)) {
         return BooleanLattice.getInstance();
      } else {
         return null;
      }
   }

   @Override
   public Name name() {
      return RULE_NAME;
   }

   @Override
   public String displayName() {
      return DISPLAY_NAME;
   }
   
   @Override
   public String toString() {
      return DISPLAY_NAME;
   }
}
