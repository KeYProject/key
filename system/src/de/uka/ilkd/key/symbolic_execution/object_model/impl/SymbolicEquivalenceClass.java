package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;

/**
 * Default implementation of {@link ISymbolicEquivalenceClass}.
 * @author Martin Hentschel
 */
public class SymbolicEquivalenceClass implements ISymbolicEquivalenceClass {
   /**
    * The {@link Services} to use.
    */
   private Services services;
   
   /**
    * The contained {@link Term}s which represents the same {@link ISymbolicObject}.
    */
   private ImmutableList<Term> terms;

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    */
   public SymbolicEquivalenceClass(Services services) {
      this(services, ImmutableSLList.<Term>nil());
   }

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param terms The contained {@link Term}s which represents the same {@link ISymbolicObject}.
    */
   public SymbolicEquivalenceClass(Services services, ImmutableList<Term> terms) {
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
    * Checks if a {@link Term} is contained.
    * @param term The {@link Term} to check.
    * @return {@code true} {@link Term} is contained, {@code false} {@link Term} is not contained.
    */
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
         StringBuffer sb = ProofSaver.printTerm(term, services, true);
         strings = strings.append(sb.toString());
      }
      return strings;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getRepresentative() {
      return terms.head();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getRepresentativeString() {
      Term representative = getRepresentative();
      if (representative != null) {
         StringBuffer sb = ProofSaver.printTerm(representative, services, true);
         return sb.toString();
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
