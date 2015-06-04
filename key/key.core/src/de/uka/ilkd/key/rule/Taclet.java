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

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.LemmaJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.executor.javadl.TacletExecutor;
import de.uka.ilkd.key.rule.match.TacletMatcherKit;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;


/** 
 * Taclets are the DL-extension of schematic theory specific rules. They are
 * used to describe rules of a logic (sequent) calculus. A typical taclet
 * definition looks similar to <br></br>
 * <code> 
 *    taclet_name { if ( ... ) find ( ... ) goal_descriptions }
 * </code> <br></br>
 * where the if-part must and the find-part can contain a sequent arrow, that
 * indicates, if a term has to occur at the top level and if so, on which side of
 * the sequent. The goal descriptions consists of lists of add and replacewith
 * constructs. They describe, how to construct a new goal out of the old one by
 * adding or replacing parts of the sequent. Each of these lists describe a new
 * goal, whereas if no such list exists, means that the goal is closed. <p>
 *   The find part of a taclet is used to attached the rule to a term in the
 * sequent of the current goal. Therefore the term of the sequent has to match
 * the schema as found in the taclet's find part. The taclet is then attached to
 * this term, more precise not the taclet itself, but an application object of
 * this taclet (see {@link de.uka.ilkd.key.rule.TacletApp TacletApp}. When
 * this attached taclet application object is applied, the new goals are
 * constructed as described by the goal descriptions. For example <br></br>
 * <code> 
 *    find (A | B ==>) replacewith ( A ==> ); replacewith(B ==>) 
 * </code> <br></br>creates 
 * two new goals, where the first has been built by replacing <code> A | B </code>
 * with <code>A</code> and the second one by replacing <code>A | B</code> with
 * <code>B</code>. For a complete description of the syntax and semantics of
 * taclets consult the KeY-Manual.  The objects of this class serve different
 * purposes: First they represent the syntactical structure of a taclet, but 
 * they also include the taclet interpreter isself. The taclet interpreter
 * knows two modes: the match and the execution mode. The match mode tries to
 * find a a mapping from schemavariables to a given term or formula. In the
 * execution mode, a given goal is manipulated in the manner as described by the
 * goal descriptions. </p>
 * <p>
 *   But an object of this class neither copies or split the goal, nor it
 * iterates through a sequent looking where it can be applied, these tasks have
 * to be done in advance. For example by one of the following classes 
 * {@link de.uka.ilkd.key.proof.RuleAppIndex RuleAppIndex} or 
 * {@link de.uka.ilkd.key.proof.TacletAppIndex TacletAppIndex} or 
 * {@link de.uka.ilkd.key.rule.TacletApp TacletApp} </p>
 */
public abstract class Taclet implements Rule, Named {
   
   protected final ImmutableSet<TacletAnnotation> tacletAnnotations;

   public RuleJustification getRuleJustification() {
      if (tacletAnnotations.contains(TacletAnnotation.LEMMA)) {
         return LemmaJustification.INSTANCE;
      }
      else {
         return AxiomJustification.INSTANCE;
      }
   }
    
    /** name of the taclet */
    private final Name name;
    
    /** name displayed by the pretty printer */
    private final String displayName;
    
    /** the set of taclet options for this taclet */
    protected final ImmutableSet<Choice> choices;
    
    /**
     * the <tt>if</tt> sequent of the taclet
     */
    private final Sequent ifSequent;
    
    /** 
     * Variables that have to be created each time the taclet is applied. 
     * Those variables occur in the varcond part of a taclet description.
     */
    private final ImmutableList<NewVarcond> varsNew;
    /** 
     * variables with a "x not free in y" variable condition. This means the
     * instantiation of VariableSV x must not occur free in the instantiation of
     * TermSV y.
     */
    private final ImmutableList<NotFreeIn> varsNotFreeIn;
    /** 
     * variable conditions used to express that a termsv depends on the free
     * variables of a given formula(SV)
     * Used by skolemization rules.
     */
    @Deprecated
    private final ImmutableList<NewDependingOn> varsNewDependingOn;

    /** Additional generic conditions for schema variable instantiations. */
    private final ImmutableList<VariableCondition> variableConditions;

    /**
     * the list of taclet goal descriptions 
     */
    private final ImmutableList<TacletGoalTemplate> goalTemplates;

    /**
     * list of rulesets (formerly known as heuristics) the taclet belongs to
     */
    protected final ImmutableList<RuleSet> ruleSets;

    /**
     * map from a schemavariable to its prefix. The prefix is used to test
     * correct instantiations of the schemavariables by resolving/avoiding
     * collisions. Mainly the prefix consists of a list of all variables that
     * may appear free in the instantiation of the schemavariable (a bit more
     * complicated for rewrite taclets, see paper of M:Giese)
     */
    protected final ImmutableMap<SchemaVariable,TacletPrefix> prefixMap;
    
    /** cache; contains set of all bound variables */
    private ImmutableSet<QuantifiableVariable> boundVariables = null;
    
    /** tracks state of pre-computation */
    private boolean contextInfoComputed = false;
    private boolean contextIsInPrefix   = false;
    
    protected String tacletAsString;

    /** Set of schemavariables of the if part */
    private ImmutableSet<SchemaVariable> ifVariables = null;

    /** This map contains (a, b) if there is a substitution {b a}
     * somewhere in this taclet */
    private ImmutableMap<SchemaVariable,SchemaVariable> svNameCorrespondences = null;
	
    /** Integer to cache the hashcode */
    private int hashcode = 0;    
    
    private final Trigger trigger;
    
    /* TODO: find better solution*/
    private final boolean surviveSymbExec;
    
    
    // The two rule engines for matching and execution (application) of taclets
    // In the long run, we should think about keeping those somewhere else, e.g., in the services 
    // such that we gain more flexibility like combined matchers that do not just match one taclet but
    // all at once for a given term.
    
    /** 
     * The taclet matcher
     */
    private TacletMatcher matcher;

    /**
     * The taclet executor
     */
    protected TacletExecutor<? extends Taclet> executor;

    
    
    /**
     * creates a Taclet (originally known as Schematic Theory Specific Rules)
     * @param name the name of the Taclet 
     * @param applPart contains the application part of an Taclet that is
     * the if-sequence, the variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param ruleSets a list of rule sets for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values
     * indicating a noninteractive or recursive use of the Taclet.      
     */
    protected Taclet(Name name,
           TacletApplPart applPart,
           ImmutableList<TacletGoalTemplate> goalTemplates,
           ImmutableList<RuleSet> ruleSets,
           TacletAttributes attrs,
           ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
           ImmutableSet<Choice> choices,
           boolean surviveSmbExec,
           ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this.tacletAnnotations = tacletAnnotations;
        this.name          = name;
        ifSequent          = applPart.ifSequent();
        varsNew            = applPart.varsNew();
        varsNotFreeIn      = applPart.varsNotFreeIn();
        varsNewDependingOn = applPart.varsNewDependingOn();
        variableConditions = applPart.getVariableConditions();
        this.goalTemplates = goalTemplates;
        this.ruleSets      = ruleSets;
        this.choices       = choices;
        this.prefixMap     = prefixMap;
        this.displayName = attrs.displayName() == null
                           ? name.toString() : attrs.displayName();
        this.surviveSymbExec = surviveSmbExec;
        
        this.trigger = attrs.getTrigger();
    }

    public boolean hasTrigger() {
        return trigger != null;
    }

    public Trigger getTrigger() {
        return trigger;
    }

    public final TacletMatcher getMatcher() {
       return matcher;
    }
    
    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given
     * parameters.
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of an Taclet that is the
     * if-sequence, the variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param ruleSets a list of rule sets for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values
     * indicating a noninteractive or recursive use of the Taclet.
     */
    protected Taclet(Name name,
           TacletApplPart applPart,
           ImmutableList<TacletGoalTemplate> goalTemplates,
           ImmutableList<RuleSet> ruleSets,
           TacletAttributes attrs,
           ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
           ImmutableSet<Choice> choices,
           ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, ruleSets, attrs, prefixMap, choices, false, tacletAnnotations);
    }
      
    /**
     * creates and initializes the taclet matching and execution engines
     * has to be called at the end of initialization
     */
    protected void createTacletServices() {
        createAndInitializeMatcher();
        createAndInitializeExecutor();
    }
    
    protected void createAndInitializeMatcher() {      
        this.matcher = TacletMatcherKit.getKit().createTacletMatcher(this);
    }

    protected abstract void createAndInitializeExecutor();
    
    /** 
     * computes and returns all variables that occur bound in the taclet
     * including the taclets defined in <tt>addrules</tt> sections. The result
     * is cached and therefore only computed once.  
     * @return all variables occuring bound in the taclet
     */
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {        
        if (boundVariables == null) {        
            ImmutableSet<QuantifiableVariable> result = 
                DefaultImmutableSet.<QuantifiableVariable>nil();
                       
            for (final TacletGoalTemplate tgt : goalTemplates()) {
                result = result.union(tgt.getBoundVariables());
            }

            final BoundVarsVisitor bvv = new BoundVarsVisitor();
            bvv.visit(ifSequent());
            result = result.union(bvv.getBoundVariables()).
                    union(getBoundVariablesHelper());

            boundVariables = result;
        }
        
        return boundVariables;
    }

    /**
     * collects bound variables in taclet entities others than goal templates
     * @return set of variables that occur bound in taclet entities others 
     * than goal templates
     */
    protected abstract ImmutableSet<QuantifiableVariable> getBoundVariablesHelper(); 

    /**
     * returns true iff the taclet contains a "close goal"-statement
     * @return true iff the taclet contains a "close goal"-statement
     */
    public boolean closeGoal () {
	return goalTemplates.isEmpty();
    }

    /**
     * looks if a variable is declared as new and returns its sort to match
     * with or the schema variable it shares the match-sort with. Returns
     * null if the SV is not declared to as new.
     * @param var the SchemaVariable to look for
     * @return the sort of the SV to match or the SV it shares the same
     * match-sort with
     */
    public NewVarcond varDeclaredNew(SchemaVariable var) {
	for(final NewVarcond nv : varsNew) {
	    if(nv.getSchemaVariable() == var) {
		return nv;
	    }
	}
	return null;
    }

    /**
     * @return the generic variable conditions of this taclet
     */
    public ImmutableList<VariableCondition> getVariableConditions () {
	return variableConditions;
    }

    /** returns the name of the Taclet
     */
    public Name name() {
	return name;
    } 
    

    /** returns the display name of the taclet, or, if not specified -- 
     *  the canonical name
     */
    public String displayName() {
	return displayName;
    }
 
   /** 
    * returns the if-sequence of the application part of the Taclet.
    */
    public Sequent ifSequent() {
	return ifSequent;
    } 
    
    /** returns an iterator over the variables that are new in the Taclet. 
     */
    public ImmutableList<NewVarcond> varsNew() {
	return varsNew;
    } 

    
    /** returns an iterator over the variable pairs that indicate that are 
     * new in the Taclet. 
     */
    public ImmutableList<NotFreeIn> varsNotFreeIn() { 
	return varsNotFreeIn;
    } 
    

    public ImmutableList<NewDependingOn> varsNewDependingOn() { 
	return varsNewDependingOn;
    } 
    
    /** returns an iterator over the goal descriptions.
     */
    public ImmutableList<TacletGoalTemplate> goalTemplates() {
	return goalTemplates;
    } 

    public ImmutableSet<Choice> getChoices(){
	return choices;
    }

    /** returns an iterator over the rule sets. */
    public Iterator<RuleSet> ruleSets() {
	return ruleSets.iterator();
    } 

    public ImmutableList<RuleSet> getRuleSets() {
	return ruleSets;
    }

    public ImmutableMap<SchemaVariable,TacletPrefix> prefixMap() {
	return prefixMap;
    }

    /** 
     * returns true if one of the goal templates is a replacewith. Already
     * computed and cached by method cacheMatchInfo
     */
    public boolean hasReplaceWith() {
        for (final TacletGoalTemplate goalDescr: goalTemplates) {
            if (goalDescr.replaceWithExpressionAsObject() != null) {
                return true;
            }
        }     
        return false;
    }
    
    /**
     * returns the computed prefix for the given schemavariable. The
     * prefix of a schemavariable is used to determine if an
     * instantiation is correct, in more detail: it mainly contains all
     * variables that can appear free in an instantiation of the
     * schemvariable sv (rewrite taclets have some special handling, see
     * paper of M. Giese and comment of method isContextInPrefix).
     * @param sv the Schemavariable 
     * @return prefix of schema variable sv
     */
    public TacletPrefix getPrefix(SchemaVariable sv) {
	return prefixMap.get(sv);
    }

    /**
     * returns true iff a context flag is set in one of the entries in
     * the prefix map. Is cached after having been called
     * once. __OPTIMIZE__ is caching really necessary here?
     *
     * @return true iff a context flag is set in one of the entries in
     * the prefix map.
     */
    public boolean isContextInPrefix() {
	if (contextInfoComputed) {
	    return contextIsInPrefix;
	}
	contextInfoComputed=true;
	Iterator<TacletPrefix> it=prefixMap().valueIterator();
	while (it.hasNext()) {
	    if (it.next().context()) {
		contextIsInPrefix=true;
		return true;
	    }
	}
	contextIsInPrefix=false;
	return false;
    }

    /** 
     * return true if <code>o</code> is a taclet of the same name and 
     * <code>o</code> and <code>this</code> contain no mutually exclusive 
     * taclet options. 
     */
    public boolean equals(Object o) {
        if (o == this) return true;
        
        if (o == null || o.getClass() != this.getClass() ){
           return false;
        }	

        final Taclet t2 = (Taclet)o;
        if (!name.equals(t2.name)) { 
           return false;
        }

        if ((ifSequent == null && t2.ifSequent != null) || 
              (ifSequent != null && t2.ifSequent == null)) {
           return false;
        } else if (ifSequent != null && !ifSequent.equals(t2.ifSequent)) {
           return false;
        }
         
        if (!choices.equals(t2.choices)) {
           return false;
        }

       if (!goalTemplates.equals(t2.goalTemplates)) {
          return false;
       }
        
        return true;
    }

    public int hashCode() {
        if (hashcode == 0) {
           hashcode = 37 * name.hashCode() + 17;
            if (hashcode == 0) {
                hashcode = -1;
            }
        }
        return hashcode;
    }

    /**
     * returns the set of schemavariables of the taclet's if-part
     * @return Set of schemavariables of the if part
     */
    protected ImmutableSet<SchemaVariable> getIfVariables () {
	// should be synchronized
	if ( ifVariables == null ) {
	    TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector ();
	    svc.visit( ifSequent () );
	    
	    ifVariables                 = DefaultImmutableSet.<SchemaVariable>nil();
	    for (final SchemaVariable sv : svc.vars()) {
		  ifVariables = ifVariables.add ( sv );
	    }
	}

	return ifVariables;
    }
    
    /**
     * @return set of schemavariables of the if and the (optional)
     * find part
     */
    public abstract ImmutableSet<SchemaVariable> getIfFindVariables ();


    /**
     * Find a schema variable that could be used to choose a name for
     * an instantiation (a new variable or constant) of "p"
     * @return a schema variable that is substituted by "p" somewhere
     * in this taclet (that is, these schema variables occur as
     * arguments of a substitution operator)
     */
    public SchemaVariable getNameCorrespondent ( SchemaVariable p,
                                                 Services services) {
	// should be synchronized
	if ( svNameCorrespondences == null ) {
	    final SVNameCorrespondenceCollector c =
		new SVNameCorrespondenceCollector (services.getTypeConverter().getHeapLDT());
	    c.visit ( this, true );
	    svNameCorrespondences = c.getCorrespondences ();
	}

	return svNameCorrespondences.get ( p );
    }


    StringBuffer toStringIf(StringBuffer sb) {
        if (!ifSequent.isEmpty()) {
            sb = sb.append("\\assumes (").append(ifSequent).append(") ");
            sb = sb.append("\n");
        }
        return sb;
    }

    StringBuffer toStringVarCond(StringBuffer sb) {

        if (!varsNew.isEmpty() || !varsNotFreeIn.isEmpty() || !variableConditions.isEmpty()) {
            sb = sb.append("\\varcond(");

            int countVarsNew = varsNew.size() - 1;
            for (final NewVarcond nvc: varsNew) {
                sb = sb.append(nvc);
                if (countVarsNew > 0 || !varsNotFreeIn.isEmpty() || !variableConditions.isEmpty()) {
                    sb=sb.append(", "); 
                }
                --countVarsNew;
            }

            int countVarsNotFreeIn = varsNotFreeIn.size() - 1;
            for (NotFreeIn pair: varsNotFreeIn) {
                sb = sb.append("\\notFreeIn(").append(pair.first()).append(", ").append(pair.second()).append(")");	 
                if (countVarsNotFreeIn > 0 || !variableConditions.isEmpty()) sb = sb.append(", ");
                --countVarsNotFreeIn;
            }

            int countVariableConditions = variableConditions.size();
            for (final VariableCondition vc: variableConditions) {
                sb.append(vc);
                if (countVariableConditions > 0) sb.append(", ");
                --countVariableConditions;
            }
            sb = sb.append(")\n");	    
        }
        return sb;
    }

    StringBuffer toStringGoalTemplates(StringBuffer sb) {
        if (goalTemplates.isEmpty()) {
            sb.append("\\closegoal");
        } else {
            Iterator<TacletGoalTemplate> it=goalTemplates().iterator();
            while (it.hasNext()) {
                sb=sb.append(it.next());
                if (it.hasNext()) sb = sb.append(";");
                sb = sb.append("\n");
            }
        }
        return sb;
    }

    StringBuffer toStringRuleSets(StringBuffer sb) {
	Iterator<RuleSet> itRS=ruleSets();
	if (itRS.hasNext()) {
	    sb=sb.append("\\heuristics(");
	    while (itRS.hasNext()) {
		sb = sb.append(itRS.next());
		if (itRS.hasNext()) sb=sb.append(", ");
	    }
	    sb=sb.append(")");
	}
	return sb;
    }

    StringBuffer toStringAttribs(StringBuffer sb) {
//	if (noninteractive()) sb = sb.append(" \\noninteractive");
       sb.append("\nChoices: ").append(choices);
	return sb;
    }
    
    /**
     * returns a representation of the Taclet as String
     * @return string representation
     */
    public String toString() {
	if (tacletAsString == null) {
	    StringBuffer sb=new StringBuffer();
	    sb = sb.append(name()).append(" {\n");
	    sb = toStringIf(sb);
	    sb = toStringVarCond(sb);
	    sb = toStringGoalTemplates(sb);
	    sb = toStringRuleSets(sb);
	    sb = toStringAttribs(sb); 
	    tacletAsString = sb.append("}").toString();
	}
	return tacletAsString;
    }

    /**
     * @return true iff <code>this</code> taclet may be applied for the
     * given mode (interactive/non-interactive, activated rule sets)
     */
    public boolean admissible(boolean       interactive,
			      ImmutableList<RuleSet> p_ruleSets) {
	if ( interactive )
	    return admissibleInteractive(p_ruleSets);
	else
	    return admissibleAutomatic(p_ruleSets);
    }

    protected boolean admissibleInteractive(ImmutableList<RuleSet> notAdmissibleRuleSets) {
        return true;
    }

    protected boolean admissibleAutomatic(ImmutableList<RuleSet> admissibleRuleSets) {
        for (final RuleSet tacletRuleSet : getRuleSets() ) {
            if ( admissibleRuleSets.contains ( tacletRuleSet ) ) return true;
        }
        return false;
    }

    public boolean getSurviveSymbExec() {
        return surviveSymbExec;
    }

    public Set<SchemaVariable> collectSchemaVars() {

	Set<SchemaVariable> result = new LinkedHashSet<SchemaVariable>();
	OpCollector oc = new OpCollector();

	//find, assumes
	for(SchemaVariable sv: this.getIfFindVariables()) {
	    result.add(sv);
	}

	//add, replacewith
	for(TacletGoalTemplate tgt : this.goalTemplates()) {
	    collectSchemaVarsHelper(tgt.sequent(), oc);
	    if(tgt instanceof AntecSuccTacletGoalTemplate) {
		collectSchemaVarsHelper(
			((AntecSuccTacletGoalTemplate)tgt).replaceWith(), oc);
	    } else if(tgt instanceof RewriteTacletGoalTemplate) {
		((RewriteTacletGoalTemplate)tgt).replaceWith()
					        .execPostOrder(oc);
	    }
	}

	for(Operator op : oc.ops()) {
	    if(op instanceof SchemaVariable) {
		result.add((SchemaVariable)op);
	    }
	}

	return result;
    }
    


    private void collectSchemaVarsHelper(Sequent s, OpCollector oc) {
	for(SequentFormula cf : s) {
	    cf.formula().execPostOrder(oc);
	}
    }
    
    /**
     * Instances of this class are used as hints to maintain {@link TermLabel}s.
     * @author Martin Hentschel
     */
    public static class TacletLabelHint {
       /**
        * The currently performed operation.
        */
       private final TacletOperation tacletOperation;
       
       /**
        * The optional {@link Sequent} of the add or replace part of the taclet.
        */
       private final Sequent sequent;
       
       /**
        * The optional {@link SequentFormula} contained in {@link #getSequent()}.
        */
       private final SequentFormula sequentFormula;

       /**
        * The optional replace {@link Term} of the taclet.
        */
       private final Term term;
       
       /**
        * Constructor.
        * @param tacletOperation The currently performed operation.
        * @param sequent The optional {@link Sequent} of the add or replace part of the taclet.
        */
       public TacletLabelHint(TacletOperation tacletOperation, Sequent sequent) {
          assert tacletOperation != null;
          assert !TacletOperation.REPLACE_TERM.equals(tacletOperation);
          assert sequent != null;
          this.tacletOperation = tacletOperation;
          this.sequent = sequent;
          this.sequentFormula = null;
          this.term = null;
       }
      
       /**
        * Constructor.
        * @param tacletOperation The currently performed operation.
        * @param term The optional replace {@link Term} of the taclet.
        */
       public TacletLabelHint(Term term) {
          assert term != null;
          this.tacletOperation = TacletOperation.REPLACE_TERM;
          this.sequent = null;
          this.sequentFormula = null;
          this.term = term;
       }
      
       /**
        * Constructor.
        * @param labelHint The previous {@link TacletLabelHint} which is now specialised.
        * @param sequentFormula The optional {@link SequentFormula} contained in {@link #getSequent()}.
        */
       public TacletLabelHint(TacletLabelHint labelHint, SequentFormula sequentFormula) {
          assert labelHint != null;
          assert !TacletOperation.REPLACE_TERM.equals(labelHint.getTacletOperation());
          assert sequentFormula != null;
          this.tacletOperation = labelHint.getTacletOperation();
          this.sequent = labelHint.getSequent();
          this.sequentFormula = sequentFormula;
          this.term = labelHint.getTerm();
       }
        
       /**
        * Returns the currently performed operation.
        * @return The currently performed operation.
        */
       public TacletOperation getTacletOperation() {
          return tacletOperation;
       }

       /**
        * Returns the optional {@link Sequent} of the add or replace part of the taclet.
        * @return The optional {@link Sequent} of the add or replace part of the taclet.
        */
       public Sequent getSequent() {
          return sequent;
       }

       /**
        * Returns the optional {@link SequentFormula} contained in {@link #getSequent()}.
        * @return The optional {@link SequentFormula} contained in {@link #getSequent()}.
        */
       public SequentFormula getSequentFormula() {
          return sequentFormula;
       }

       /**
        * Returns the optional replace {@link Term} of the taclet.
        * @return The optional replace {@link Term} of the taclet.
        */
       public Term getTerm() {
          return term;
       }

       /**
        * {@inheritDoc}
        */
       @Override
       public String toString() {
          return tacletOperation + ", sequent = " + sequent + ", sequent formula = " + sequentFormula + ", term = " + term;
       }

       /**
        * Defines the possible operations a {@link Taclet} performs.
        * @author Martin Hentschel
        */
       public static enum TacletOperation {
          /**
           * Add clause of a {@link Taclet} applied to the antecedent.
           * Available information are {@link TacletLabelHint#getSequent()} and {@link TacletLabelHint#getSequentFormula()}.
           */
          ADD_ANTECEDENT, 

          /**
           * Add clause of a {@link Taclet} applied to the succedent.
           * Available information are {@link TacletLabelHint#getSequent()} and {@link TacletLabelHint#getSequentFormula()}.
           */
          ADD_SUCCEDENT, 
          
          /**
           * Replace clause of a {@link Taclet} provides a {@link Sequent} and currently additional adds to the antecedent are performed.
           * Available information are {@link TacletLabelHint#getSequent()} and {@link TacletLabelHint#getSequentFormula()}.
           */
          REPLACE_TO_ANTECEDENT, 
          
          /**
           * Replace clause of a {@link Taclet} provides a {@link Sequent} and currently the current {@link PosInOccurrence} on the succedent is modified.
           * Available information are {@link TacletLabelHint#getSequent()} and {@link TacletLabelHint#getSequentFormula()}.
           */
          REPLACE_AT_SUCCEDENT, 
          
          /**
           * Replace clause of a {@link Taclet} provides a {@link Sequent} and currently the current {@link PosInOccurrence} on the antecedent is modified.
           * Available information are {@link TacletLabelHint#getSequent()} and {@link TacletLabelHint#getSequentFormula()}.
           */
          REPLACE_AT_ANTECEDENT, 
          
          /**
           * Replace clause of a {@link Taclet} provides a {@link Sequent} and currently additional adds to the succedent are performed.
           * Available information are {@link TacletLabelHint#getSequent()} and {@link TacletLabelHint#getSequentFormula()}.
           */
          REPLACE_TO_SUCCEDENT, 

          /**
           * Replace clause of a {@link Taclet} provides a {@link Term} which is currently used to modify the {@link PosInOccurrence}.
           * Available information are {@link TacletLabelHint#getTerm()}.
           */
          REPLACE_TERM;
       }
    }
    
    /** 
     * applies the given rule application to the specified goal
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param tacletApp the rule application that is executed.
     * @return List of the goals created by the rule which have to be
     * proved. If this is a close-goal-taclet ( this.closeGoal () ),
     * the first goal of the return list is the goal that should be
     * closed (with the constraint this taclet is applied under).
     */
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp tacletApp) {
        return getExecutor().apply(goal, services, tacletApp);
    }

    public TacletExecutor<? extends Taclet> getExecutor() {
        return executor;
    }
    
    public abstract Taclet setName(String s);
}