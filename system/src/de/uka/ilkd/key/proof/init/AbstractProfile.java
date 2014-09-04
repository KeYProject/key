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

package de.uka.ilkd.key.proof.init;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelManager.TermLabelConfiguration;
import de.uka.ilkd.key.proof.DefaultGoalChooserBuilder;
import de.uka.ilkd.key.proof.DepthFirstGoalChooserBuilder;
import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooserBuilder;

public abstract class AbstractProfile implements Profile {
    /**
     * The default profile which is used if no profile is defined in custom problem files (loaded via {@link KeYUserProblemFile}).
     */
    private static Profile defaultProfile = JavaProfile.getDefaultInstance();

    private final RuleCollection       standardRules;

    private final ImmutableSet<StrategyFactory> strategies;

    private final ImmutableSet<String> supportedGC;
    private final ImmutableSet<GoalChooserBuilder> supportedGCB;

    private GoalChooserBuilder prototype;

    private TermLabelManager termLabelManager;

    private static
        ImmutableSet<String> extractNames(ImmutableSet<GoalChooserBuilder> supportedGCB) {

        ImmutableSet<String> result = DefaultImmutableSet.<String>nil();

        final Iterator<GoalChooserBuilder> it = supportedGCB.iterator();
        while (it.hasNext()) {
            result  = result.add(it.next().name());
        }

        return result;
    }

    protected AbstractProfile(String standardRuleFilename,
            ImmutableSet<GoalChooserBuilder> supportedGCB) {
        standardRules = new RuleCollection(RuleSourceFactory
                .fromBuildInRule(standardRuleFilename),
                initBuiltInRules());
        strategies = getStrategyFactories();
        this.supportedGCB = supportedGCB;
        this.supportedGC = extractNames(supportedGCB);
        this.prototype = getDefaultGoalChooserBuilder();
        assert( this.prototype!=null );
        this.termLabelManager = new TermLabelManager(computeTermLabelConfiguration());
    }

    public AbstractProfile(String standardRuleFilename) {
        this(standardRuleFilename,
                DefaultImmutableSet.<GoalChooserBuilder>nil().
                add(new DefaultGoalChooserBuilder()).
                add(new DepthFirstGoalChooserBuilder()).
                add(new SymbolicExecutionGoalChooserBuilder()));
    }

    /**
     * Computes the {@link TermLabelConfiguration} to use in this {@link Profile}.
     * @return The {@link TermLabelConfiguration} to use in this {@link Profile}.
     */
    protected abstract ImmutableList<TermLabelConfiguration> computeTermLabelConfiguration();

    public RuleCollection getStandardRules() {
        return standardRules;
    }

    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        return DefaultImmutableSet.<StrategyFactory>nil();
    }

    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        ImmutableList<BuiltInRule> builtInRules = ImmutableSLList.<BuiltInRule>nil();

	
	//Collection<SMTRule> rules = SMTSettings.getInstance().getSMTRules();
        
	//for(SMTRule rule : rules){
	  //  builtInRules = builtInRules.prepend(rule);  
	//}     
        
     
        
        
        
        return builtInRules;
    }


    public ImmutableSet<StrategyFactory> supportedStrategies() {
        return strategies;
    }

    public boolean supportsStrategyFactory(Name strategy) {
        return getStrategyFactory(strategy) != null;
    }

    public StrategyFactory getStrategyFactory(Name n) {
        Iterator<StrategyFactory> it = getStrategyFactories().iterator();
        while (it.hasNext()) {
            final StrategyFactory sf = it.next();
            if (sf.name().equals(n)) {
                return sf;
            }
        }
        return null;
    }

    /**
     * returns the names of the supported goal chooser
     * builders
     */
     public ImmutableSet<String> supportedGoalChoosers() {
         return supportedGC;
     }

     /**
      * returns the default builder for a goal chooser
      * @return this implementation returns a new instance of
      * {@link DefaultGoalChooserBuilder}
      */
     public GoalChooserBuilder getDefaultGoalChooserBuilder() {
         return new DefaultGoalChooserBuilder();
     }

     /**
      * sets the user selected goal chooser builder to be used as prototype
      * @throws IllegalArgumentException if a goal chooser of the given name is not
      *  supported
      */
     public void setSelectedGoalChooserBuilder(String name) {

         this.prototype = lookupGC(name);

         if (this.prototype == null) {
             throw new IllegalArgumentException("Goal chooser:" + name +
                     " is not supported by this profile.");
         }
     }

     /**
      * looks up the demanded goal chooser is supported and returns a
      * new instance if possible otherwise <code>null</code> is returned
      *
      * @param name the String with the goal choosers name
      * @return a new instance of the builder or <code>null</code> if the
      * demanded chooser is not supported
      */
     public GoalChooserBuilder lookupGC(String name) {
        final Iterator<GoalChooserBuilder> it  = supportedGCB.iterator();
        while (it.hasNext()) {
            final GoalChooserBuilder supprotedGCB = it.next();
            if (supprotedGCB.name().equals(name)) {
                return supprotedGCB.copy();
            }
        }
        return null;
    }

    /**
      * returns a copy of the selected goal chooser builder
      */
     public GoalChooserBuilder getSelectedGoalChooserBuilder(){
        return prototype.copy();
     }

     /**
      * any standard rule has is by default justified by an axiom rule
      * justification
      * @return the justification for the standard rules
      */
     public RuleJustification getJustification(Rule r) {
         return AxiomJustification.INSTANCE;
     }
     
     
     @Override
     public String getInternalClassDirectory() {
 	return "";
     }     


     @Override
     public String getInternalClasslistFilename() {
	 return "JAVALANG.TXT";
     }

   /**
    * <p>
    * Returns the {@link Profile} for the given name.
    * </p>
    * <p>
    * It is typically used in the {@link Thread} of the user interface.
    * Other instances of this class are typically only required to 
    * use them in different {@link Thread}s (not the UI {@link Thread}).
    * </p>
    * @param name The name of the requested {@link Profile}.
    * @return The {@link Profile} with the given name for usage in the {@link Thread} of the user interface or {@code null} if not available.
    */
   public static Profile getDefaultInstanceForName(String name) {
      if (JavaProfile.NAME.equals(name)) {
         return JavaProfile.getDefaultInstance();
      }
      else if (SymbolicExecutionJavaProfile.NAME.equals(name)) {
         return SymbolicExecutionJavaProfile.getDefaultInstance();
      }
      else {
         return null;
      }
   }

   /**
    * Returns the default profile which is used if no profile is defined in custom problem files (loaded via {@link KeYUserProblemFile}).
    * @return The default profile which is used if no profile is defined in custom problem files (loaded via {@link KeYUserProblemFile}).
    */
   public static Profile getDefaultProfile() {
      return defaultProfile;
   }

   /**
    * Sets the default profile which is used if no profile is defined in custom problem files (loaded via {@link KeYUserProblemFile}).
    * @param defaultProfile The default profile which is used if no profile is defined in custom problem files (loaded via {@link KeYUserProblemFile}).
    */
   public static void setDefaultProfile(Profile defaultProfile) {
      assert defaultProfile != null;
      AbstractProfile.defaultProfile = defaultProfile;
   }

   @Override
   public TermLabelManager getTermLabelManager() {
       return termLabelManager;
   }
}