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

package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * Default implementation of {@link ISymbolicEquivalenceClass}.
 * @author Martin Hentschel
 */
public class SymbolicEquivalenceClass extends AbstractElement implements ISymbolicEquivalenceClass {
   /**
    * The {@link Services} to use.
    */
   private final Services services;
   
   /**
    * The contained {@link Term}s which represents the same {@link ISymbolicObject}.
    */
   private ImmutableList<Term> terms;

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicEquivalenceClass(Services services, IModelSettings settings) {
      this(services, ImmutableSLList.<Term>nil(), settings);
   }

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param terms The contained {@link Term}s which represents the same {@link ISymbolicObject}.
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicEquivalenceClass(Services services, ImmutableList<Term> terms, IModelSettings settings) {
      super(settings);
      this.services = services;
      this.terms = terms;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Term> getTerms() {
      return terms;
   }
   
   /**
    * Adds a new {@link Term}.
    * @param value The new {@link Term} to add.
    */
   public void addTerm(Term term) {
      terms = terms.append(term);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean containsTerm(Term term) {
      return terms.contains(term);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<String> getTermStrings() {
      ImmutableList<String> strings = ImmutableSLList.nil();
      for (Term term : terms) {
         strings = strings.append(formatTerm(term, services));
      }
      return strings;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getRepresentative() {
      // Prefer null if contained in equivalence class
      final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
      Term nullTerm = JavaUtil.search(terms, new IFilter<Term>() {
         @Override
         public boolean select(Term element) {
            return element.op() == heapLDT.getNull();
         }
      });
      if (nullTerm != null) {
         return nullTerm;
      }
      else {
         // Prefer terms which are a program variable
         Term representative = JavaUtil.search(terms, new IFilter<Term>() {
            @Override
            public boolean select(Term element) {
               return element.op() instanceof IProgramVariable;
            }
         });
         return representative != null ? 
                representative : // Return term with program variable 
                terms.head(); // Return the first term
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getRepresentativeString() {
      Term representative = getRepresentative();
      if (representative != null) {
         return formatTerm(representative, services);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Equivalence Class " + getTermStrings();
   }
}