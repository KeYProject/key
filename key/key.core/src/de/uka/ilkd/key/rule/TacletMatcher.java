package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public interface TacletMatcher {

   /** returns a SVInstantiations object with the needed SchemaVariable to Term
    * mappings to match the given Term template to the Term term or
    * null if no matching is possible.
    * (marked as final to help the compiler inlining methods)
    * @param term the Term the Template should match
    * @param template the Term tried to be instantiated so that it matches term
    * @param matchCond the MatchConditions to be obeyed by a
    * successful match
    * @return the new MatchConditions needed to match template with
    * term, if possible, null otherwise
    *
    * PRECONDITION: matchCond.getConstraint ().isSatisfiable ()
    */
   public abstract MatchConditions match(Term term, Term template,
         MatchConditions matchCond, Services services);

   /**
    * Match the given template (which is probably a formula of the if
    * sequence) against a list of constraint formulas (probably the
    * formulas of the antecedent or the succedent), starting with the
    * given instantiations and constraint p_matchCond.
    * @param p_toMatch list of constraint formulas to match p_template to
    * @param p_template template formula as in "match"
    * @param p_matchCond already performed instantiations
    * @param p_services the Services object encapsulating information
    * about the java datastructures like (static)types etc.
    * @return Two lists (in an IfMatchResult object), containing the
    * the elements of p_toMatch that could successfully be matched
    * against p_template, and the corresponding MatchConditions.
    */
   public abstract IfMatchResult matchIf(
         Iterable<IfFormulaInstantiation> p_toMatch, Term p_template,
         MatchConditions p_matchCond, Services p_services);

   /**
    * Match the whole if sequent using the given list of
    * instantiations of all if sequent formulas, starting with the
    * instantiations given by p_matchCond.
    * PRECONDITION: p_toMatch.size () == ifSequent ().size ()
    * @return resulting MatchConditions or null if the given list
    * p_toMatch does not match
    */
   public abstract MatchConditions matchIf(
         Iterable<IfFormulaInstantiation> p_toMatch,
         MatchConditions p_matchCond, Services p_services);

   /**
    * checks the provided matches against the variable conditions of this taclet
    * It returns the resulting match conditions or <code>null</code> if the found matches
    * do not satisfy the variable conditions. If the given matchconditions are <code>null</code>
    * then <code>null</code> is returned
    * @param p_matchconditions the matches to be checked
    * @param services the {@link Services}
    * @return the resulting match conditions or <code>null</code> if 
    * given matches do not satisfy the taclet's variable conditions   
    */
   public abstract MatchConditions checkConditions(MatchConditions p_matchconditions, Services services);

   /**
    * checks if the conditions for a correct instantiation are satisfied
    * @param var the SchemaVariable to be instantiated
    * @param instantiationCandidate the SVSubstitute, which is a
    * candidate for a possible instantiation of var
    * @param matchCond the MatchConditions which have to be respected
    * for the new match
    * @param services the Services object encapsulating information
    * about the Java type model
    * @return the match conditions resulting from matching
    * <code>var</code> with <code>instantiationCandidate</code> or
    * <code>null</code> if a match was not possible
    */
   public abstract MatchConditions checkVariableConditions(SchemaVariable var, SVSubstitute instantiationCandidate,
         MatchConditions matchCond, Services services);

}