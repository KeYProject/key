package de.uka.ilkd.key.rule.match.legacy;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.IfMatchResult;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NotFreeIn;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletMatcher;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.match.TacletMatcherKit;
import de.uka.ilkd.key.util.Pair;

/** 
 * This class encapsulates the matching logic for taclet's.
 * 
 * Instances of this class should <strong>not</strong> be created directly, use
 * {@link TacletMatcherKit#createTacletMatcher(Taclet)} instead.
 * @see TacletMatcherKit
 */
public final class LegacyTacletMatcher implements TacletMatcher {

    private final ImmutableList<VariableCondition> varconditions;
    private final Sequent assumesSequent;
    private final ImmutableSet<QuantifiableVariable> boundVars;
    private final ImmutableList<NotFreeIn> varsNotFreeIn;
    
    private final boolean ignoreTopLevelUpdates;
    private final Term findExp;
   
    /**
     * @param taclet the Taclet matched by this matcher
     */
    public LegacyTacletMatcher(Taclet taclet) {
        varconditions = taclet.getVariableConditions();
        assumesSequent = taclet.ifSequent();
        boundVars = taclet.getBoundVariables();
        varsNotFreeIn = taclet.varsNotFreeIn();

        if (taclet instanceof FindTaclet) {
            ignoreTopLevelUpdates = ((FindTaclet) taclet).ignoreTopLevelUpdates();
            findExp = ((FindTaclet) taclet).find();
        } else {
            ignoreTopLevelUpdates = false;
            findExp = null;
        }     
    }
    
   
    /**
     * tries to match the bound variables of the given term against the one
     * described by the template
     * @param term the Term whose bound variables are matched against the
     * JavaBlock of the template
     * (marked as final to help the compiler inlining methods)
     * @param template the Term whose bound variables are the template that have
     * to be matched
     * @param matchCond the MatchConditions that has to be paid respect when
     * trying to match
     * @return the new matchconditions if a match is possible, otherwise null
     */
    private final MatchConditions matchBoundVariables(Term term, 
            Term template, 
            MatchConditions matchCond,
            Services services) {

        matchCond = matchCond.extendRenameTable();

        for (int j=0, arity = term.arity(); j<arity && matchCond != null; j++) {    

            ImmutableArray<QuantifiableVariable> bound    = term.varsBoundHere(j);
            ImmutableArray<QuantifiableVariable> tplBound = template.varsBoundHere(j); 

            if (bound.size() == tplBound.size()) {
                for (int i=0, boundSize = bound.size(); i<boundSize && matchCond != null; i++) {      
                    final QuantifiableVariable templateQVar = tplBound.get(i);
                    final QuantifiableVariable qVar = bound.get(i);
                    if (templateQVar instanceof LogicVariable) {
                        final RenameTable rt = matchCond.renameTable();                   
                        if (!rt.containsLocally(templateQVar) && !rt.containsLocally(qVar)) {                           
                            matchCond = matchCond.addRenaming(templateQVar, qVar);
                        }
                    }
                    matchCond = ElementMatcher.getElementMatcherFor(templateQVar).match(templateQVar, qVar, matchCond, services);               
                }
            } else {
                matchCond = null;
            }
        }
        return matchCond;
    }

    /**
     * returns the matchconditions that are required if the java block of the
     * given term matches the schema given by the template term or null if no
     * match is possible
     * (marked as final to help the compiler inlining methods)
     * @param term the Term whose JavaBlock is matched against the JavaBlock of
     * the template
     * @param template the Term whose JavaBlock is the template that has to
     * be matched
     * @param matchCond the MatchConditions that has to be paid respect when
     * trying to match the JavaBlocks
     * @param services the Services object encapsulating information about the
     * program context
     * @return the new matchconditions if a match is possible, otherwise null
     */
    protected final MatchConditions matchJavaBlock(Term term, 
            Term template, MatchConditions matchCond, Services services) {

        final JavaBlock candidateJavaBlock = term.javaBlock();
        final JavaBlock templateJavaBlock  = template.javaBlock();
        if (candidateJavaBlock.isEmpty()) { 
            if (templateJavaBlock.isEmpty()){
                if (templateJavaBlock.program() instanceof ContextStatementBlock) {
                    // we must match empty context blocks too
                    matchCond = templateJavaBlock.program().
                            match(new SourceData(candidateJavaBlock.program(), -1, services), matchCond);
                }
            } else {
                matchCond = null;
            }
        } else { //both java blocks not empty                            
            matchCond = templateJavaBlock.program().
                    match(new SourceData(candidateJavaBlock.program(), -1, services), matchCond);
        }

        return matchCond;
    }

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

    private MatchConditions match(final Term             term,
            final Term             template, 
            MatchConditions        matchCond,
            final Services         services) {
        final Operator sourceOp   =     term.op ();
        final Operator templateOp = template.op ();

        if (template.hasLabels()) {
            final ImmutableArray<TermLabel> labels = template.getLabels();

            for (TermLabel l: labels) {
                // ignore all labels which are not schema variables
                // if intended to match concrete label, match against schema label
                // and use an appropriate variable condition
                if (l instanceof SchemaVariable) {
                    final SchemaVariable schemaLabel = (SchemaVariable) l;
                    final MatchConditions cond =
                            ElementMatcher.getElementMatcherFor(schemaLabel).match(schemaLabel, term, matchCond, services);
                    if (cond == null) {
                        return null;
                    }
                    matchCond = cond;
                }
            }
        }

        if (templateOp instanceof SchemaVariable && templateOp.arity() == 0) {            
            matchCond = ElementMatcher.getElementMatcherFor(templateOp).match(templateOp, term, matchCond, services);
            return matchCond;
        }

        matchCond = ElementMatcher.getElementMatcherFor(templateOp).match (templateOp, sourceOp, matchCond, services);
        if(matchCond != null) {
            //match java blocks:
            matchCond = matchJavaBlock(term, template, matchCond, services);
            if (matchCond != null) {
                //match bound variables:
                matchCond = matchBoundVariables(term, template, matchCond, services);
                // match sub terms
                for (int i = 0, arity = term.arity(); i < arity && matchCond != null; i++) {
                    matchCond = match(term.sub(i), template.sub(i), matchCond, services);
                }
                if (matchCond != null) {
                    matchCond = matchCond.shrinkRenameTable();
                }
            } 
        }

        return matchCond; 
    }


    /** (non-Javadoc)
     * @see de.uka.ilkd.key.rule.TacletMatcher#matchIf(java.util.Iterator, de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    @Override
    public final IfMatchResult matchIf (   Iterable<IfFormulaInstantiation> p_toMatch,
            Term                             p_template,
            MatchConditions                  p_matchCond,
            Services                         p_services ) {
        ImmutableList<IfFormulaInstantiation> resFormulas = ImmutableSLList.<IfFormulaInstantiation>nil();
        ImmutableList<MatchConditions> resMC = ImmutableSLList.<MatchConditions>nil();

        Term updateFormula;
        if (p_matchCond.getInstantiations().getUpdateContext().isEmpty())
            updateFormula = p_template;
        else
            updateFormula = p_services.getTermBuilder().applyUpdatePairsSequential(p_matchCond.getInstantiations()
                    .getUpdateContext(), p_template);

        for (IfFormulaInstantiation cf: p_toMatch) {
            final MatchConditions newMC = checkConditions(match(cf.getConstrainedFormula().formula(), updateFormula, p_matchCond, p_services), p_services);
            if (newMC != null) {
                resFormulas = resFormulas.prepend(cf);
                resMC       = resMC.prepend(newMC);
            }
        }

        return new IfMatchResult ( resFormulas, resMC );
    }


    /**
     * @see de.uka.ilkd.key.rule.TacletMatcher#matchIf(java.lang.Iterable, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)    
     */
    @Override
    public final MatchConditions matchIf ( Iterable<IfFormulaInstantiation> p_toMatch,
            MatchConditions                  p_matchCond,
            Services                         p_services ) {
        final Iterator<SequentFormula>     itIfSequent   = assumesSequent .iterator ();

        ImmutableList<MatchConditions>            newMC;   

        for (final IfFormulaInstantiation candidateInst: p_toMatch) {
            assert itIfSequent.hasNext() : "p_toMatch and assumes sequent must have same number of elements";
            newMC = matchIf ( ImmutableSLList.<IfFormulaInstantiation>nil()
                    .prepend ( candidateInst ),
                    itIfSequent.next ().formula (),
                    p_matchCond,
                    p_services ).getMatchConditions ();

            if ( newMC.isEmpty() )
                return null;

            p_matchCond = newMC.head ();
        }

        assert !itIfSequent.hasNext() : "p_toMatch and assumes sequent must have same number of elements";
        
        return p_matchCond;
    }

    /**
     * {@inheritDoc}
     */
    public final MatchConditions checkConditions(MatchConditions cond, Services services) {
        MatchConditions result = cond;
        if (result != null) {
            final Iterator<SchemaVariable> svIterator = 
                    cond.getInstantiations().svIterator();

            if (!svIterator.hasNext()) {
                return checkVariableConditions(null, null, cond, services);//XXX
            }

            while (result != null && svIterator.hasNext()) {
                final SchemaVariable sv = svIterator.next();
                final Object o = result.getInstantiations().getInstantiation(sv);
                if (o instanceof SVSubstitute) {
                    result = checkVariableConditions(sv, (SVSubstitute)o , result, services);
                }
            }
        }

        return result;
    }

    /**
     * looks if a variable is declared as not free in
     * @param var the SchemaVariable to look for
     * @return true iff declared not free
     */
    private boolean varDeclaredNotFree(SchemaVariable var) {
       for (final NotFreeIn nfi : varsNotFreeIn) {
          if (nfi.first() == var) {
             return true;
          }
       }
       return false;
    }


    /**
     * returns true iff the given variable is bound either in the
     * ifSequent or in 
     * any part of the TacletGoalTemplates
     * @param v the bound variable to be searched 
     */
    private boolean varIsBound(SchemaVariable v) {
        return (v instanceof QuantifiableVariable) && boundVars.contains((QuantifiableVariable) v);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions checkVariableConditions(SchemaVariable var, 
            SVSubstitute instantiationCandidate,
            MatchConditions matchCond,
            Services services) {        
        if (matchCond != null) {
            if (instantiationCandidate instanceof Term) {
                final Term term = (Term) instantiationCandidate;
                if (!(term.op() instanceof QuantifiableVariable)) {
                    if (varIsBound(var) || varDeclaredNotFree(var)) {
                        // match(x) is not a variable, but the corresponding template variable is bound
                        // or declared non free (so it has to be matched to a variable)       
                        return null; // FAILED
                    }
                }
            }
            // check generic conditions
            for (final VariableCondition vc : varconditions) {
                matchCond = vc.check(var, instantiationCandidate, matchCond, services);       
                if (matchCond == null) {       
                    return null; // FAILED
                }
            }
        }
        return matchCond; 
    }
    
    /**
     * ignores a possible update prefix
     * @param term the term to be matched
     * @param template the pattern term
     * @param matchCond the accumulated match conditions for a successful match
     * @param services the Services
     * @return a pair of updated match conditions and the unwrapped term without the ignored updates (Which have been added to the update context in the match conditions)
     */
    private Pair<Term,MatchConditions> matchAndIgnoreUpdatePrefix(final Term term,
            final Term template, MatchConditions matchCond, final TermServices services) {

        final Operator sourceOp   = term.op ();
        final Operator templateOp = template.op ();

        if ( sourceOp instanceof UpdateApplication
                && !(templateOp instanceof UpdateApplication) ) {
            // updates can be ignored
            Term update = UpdateApplication.getUpdate(term);
            matchCond = matchCond
                    .setInstantiations ( matchCond.getInstantiations ().
                            addUpdate (update, term.getLabels()) );
            return matchAndIgnoreUpdatePrefix(UpdateApplication.getTarget(term), 
                    template, matchCond, services);       
        } else {
            return new Pair<Term, MatchConditions>(term, matchCond);
        }
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions matchFind(Term term, 
            MatchConditions matchCond,
            Services services) {
        
        if (findExp != null) {
            if (ignoreTopLevelUpdates) {
                Pair</* term below updates */Term, MatchConditions> resultUpdateMatch = 
                        matchAndIgnoreUpdatePrefix(term, findExp, matchCond, services);
                term = resultUpdateMatch.first;
                matchCond = resultUpdateMatch.second;
            }
            matchCond = checkConditions(match(term, findExp, matchCond, services), services);
        } else {
            matchCond = null;
        }
        
        return matchCond; 
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions matchSV(SchemaVariable sv, Term term,
            MatchConditions matchCond, Services services) {
        MatchConditions cond = matchCond;

        if (sv.arity() == 0) {
            cond = ElementMatcher.getElementMatcherFor(sv).match(sv, term, cond, services);
        } else {
            cond = ElementMatcher.getElementMatcherFor(sv).match(sv, term.op(), cond, services);
        }

        if (cond != null) {
            cond = checkVariableConditions(sv, term, cond, services); 
        }

        return cond; 
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions matchSV(SchemaVariable sv, ProgramElement pe,
            MatchConditions matchCond, Services services) {        
        matchCond = ElementMatcher.getElementMatcherFor(sv).match(sv, pe, matchCond, services);
        
        if (matchCond != null) {
            matchCond = checkConditions(matchCond, services);
        }
        
        return matchCond;
    }

}