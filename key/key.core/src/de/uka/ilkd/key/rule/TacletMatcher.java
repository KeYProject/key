package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public interface TacletMatcher {

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
   public abstract MatchConditions checkVariableConditions(SchemaVariable var, 
           SVSubstitute instantiationCandidate,
           MatchConditions matchCond, Services services);

   /** 
    * matches the given term against the taclet's find term 
    * if the taclet has no find term or the match is unsuccessful <code>null</null>
    * is returned
    * @param term the Term to be matched against the find expression 
    * of the taclet
    * @param matchCond the MatchConditions with side conditions to be 
    * satisfied, eg. partial instantiations of schema variables; before
    * calling this method the constraint contained in the match conditions
    * must be ensured to be satisfiable, i.e.
    *       <tt> matchCond.getConstraint ().isSatisfiable () </tt>
    * must return true
    * @param services the Services 
    * @return the found schema variable mapping or <tt>null</tt> if 
    * the matching failed
    */
   public abstract MatchConditions matchFind(Term term, MatchConditions matchCond, Services services);
   
   
   /** 
    * checks whether the given {@link SchemaVariable} {@code sv} matches the {@link Term} {@code term} w.r.t.
    * the constraints (e.g., previous matches of {@code sv}) specified in the {@link MatchConditions} {@code matchCond}
    * @param sv the {@link SchemaVariable} 
    * @param term the {@link Term} as a candidate for instantition of {@code sv} 
    * @param matchCond the {@link MatchConditions} with additional constraints that need to be considered
    * @param services the {@link Services}
    * @return {@code null} if the match is not possible or the new {@link MatchConditions} with the instantiation {@code sv <- term} added
    */
   public abstract MatchConditions matchSV(SchemaVariable sv, Term term, MatchConditions matchCond, Services services);

   /** 
    * checks whether the given {@link SchemaVariable} {@code sv} matches the {@link ProgramElement} {@code pe} w.r.t.
    * the constraints (e.g., previous matches of {@code sv}) specified in the {@link MatchConditions} {@code matchCond}
    * @param sv the {@link SchemaVariable} 
    * @param pe the {@link ProgramElement} as a candidate for instantition of {@code sv} 
    * @param matchCond the {@link MatchConditions} with additional constraints that need to be considered
    * @param services the {@link Services}
    * @return {@code null} if the match is not possible or the new {@link MatchConditions} with the instantiation {@code sv <- term} added
    */
   public abstract MatchConditions matchSV(SchemaVariable sv, ProgramElement term, MatchConditions matchCond, Services services);


}