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


package de.uka.ilkd.key.proof.init;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;

/**
 * an instance of this class describes the initial configuration of the prover.
 * This includes sorts, functions, heuristics, and variables namespaces,
 * information on the underlying java model, and a set of rules.
 */
public class InitConfig {

    /**
     * the services class allowing to access information about the underlying
     * program model
     */
    private final Services services;

    /**
     * the proof environment this init config belongs to
     */
    private final ProofEnvironment env;


    private ImmutableSet<Taclet> taclets = DefaultImmutableSet.<Taclet>nil();

    /**
     * maps categories to their default choice (both represented as Strings),
     * which is used if no other choice is specified in the problemfile
     */
    private HashMap<String,String> category2DefaultChoice =
        new LinkedHashMap<String,String>();

    /**
     * maps taclets to their TacletBuilders. This information is needed when
     * a taclet contains GoalTemplates annotated with taclet-options because
     * in this case a new taclet has to be created containing only those
     * GoalTemplates whose options are activated and those who don't belong
     * to any specific option.
     */
    private HashMap<Taclet, TacletBuilder> taclet2Builder =
        new LinkedHashMap<Taclet, TacletBuilder>();

    /**
     * Set of the rule options activated for the current proof. The rule options
     * ({@link Choice}s) allow to use different ruleset modelling or skipping
     * certain features (e.g. nullpointer checks when resolving references)
     */
    private ImmutableSet<Choice> activatedChoices 
    	= DefaultImmutableSet.<Choice>nil();

    /** HashMap for quick lookups taclet name->taclet */
    private HashMap<Name, Named> quickTacletMap;

    private String originalKeYFileName;
    
    private ProofSettings settings;    



    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public InitConfig(Services services) {
	this.services  = services;
	this.env       = new ProofEnvironment(this);
		
        category2DefaultChoice = ProofSettings.DEFAULT_SETTINGS
                                              .getChoiceSettings()
        	                              .getDefaultChoices();
  	    for(LDT ldt : getServices().getTypeConverter().getModels()) {
  		  ldt.proofSettingsUpdated(ProofSettings.DEFAULT_SETTINGS);
  	    }
    }

           
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    /**
     * returns the Services of this initial configuration providing access
     * to the used program model
     * @return the Services of this initial configuration
     */
    public Services getServices() {
        return services;
    }


    public Profile getProfile() {
	return services.getProfile();
    }


    /**
     * returns the proof environment using this initial configuration
     * @return the ProofEnvironment using this configuration
     */
    public ProofEnvironment getProofEnv() {
	assert env.getInitConfig() == this;
        return env;
    }


    /**
     * adds entries to the HashMap that maps categories to their
     * default choices.
     * Only entries of <code>init</init> with keys not already contained in
     * category2DefaultChoice are added.
     */
    public void addCategory2DefaultChoices(HashMap<String,String> init) {
        boolean changed = false;
        for (final Map.Entry<String, String> entry : init.entrySet()) {
            if(!category2DefaultChoice.containsKey(entry.getKey())) {
                changed=true;
                category2DefaultChoice.put(entry.getKey(), entry.getValue());
            }
        }
        if(changed) {
            @SuppressWarnings("unchecked")
            HashMap<String, String> clone = (HashMap<String, String>)category2DefaultChoice.clone();
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().
                setDefaultChoices(clone);
        }
    }


    public void setTaclet2Builder(HashMap<Taclet, TacletBuilder> taclet2Builder){
        this.taclet2Builder = taclet2Builder;
    }


    /**
     * {@link Taclet}s are constructed using {@link TacletBuilder}s this map
     * contains the pair of a taclet and its builder which is important as
     * goals of a taclet may depend of the selected choices. Instead of
     * creating all possible combinations in advance this is done by demand
     * @return the map from a taclet to its builder
     */
    public HashMap<Taclet, TacletBuilder> getTaclet2Builder(){
        return taclet2Builder;
    }


    /**
     * sets the set of activated choices of this initial configuration.
     * For categories without a specified choice the default choice contained
     * in category2DefaultChoice is added.
     */
    public void setActivatedChoices(ImmutableSet<Choice> activatedChoices) {
        category2DefaultChoice =
	    ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().
	    getDefaultChoices();

        @SuppressWarnings("unchecked")
        HashMap<String, String> c2DC = (HashMap<String,String>)category2DefaultChoice.clone();
        for (final Choice c : activatedChoices) {
            c2DC.remove(c.category());
        }

        for (final String s : c2DC.values()) {
            final Choice c = (Choice) choiceNS().lookup(new Name(s));
            if(c!=null){
                activatedChoices = activatedChoices.add(c);
            }
        }
        this.activatedChoices = activatedChoices;

        // invalidate quick taclet cache
        quickTacletMap = null;
    }


    /** Returns the choices which are currently active.
     * For getting the active choices for a specific proof,
     * <code>getChoices</code> in <code>de.uka.ilkd.key.proof.Proof
     * </code> has to be used.
     */
    public ImmutableSet<Choice> getActivatedChoices() {
        return activatedChoices;
    }


    public void setTaclets(ImmutableSet<Taclet> taclets){
        this.taclets = taclets;
    }


    public ImmutableSet<Taclet> getTaclets(){
        return taclets;
    }


    public Taclet lookupActiveTaclet(Name name) {
	if (quickTacletMap == null) {
            quickTacletMap = new LinkedHashMap<Name, Named>();
            Iterator<Taclet> it = activatedTaclets().iterator();
            while (it.hasNext())  {
                Taclet t = it.next();
                quickTacletMap.put(t.name(), t);
            }
        }

        return (Taclet) quickTacletMap.get(name);
    }


    /**
     * returns the activated taclets of this initial configuration
     */
    public ImmutableSet<Taclet> activatedTaclets() {
        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();
        TacletBuilder b;

        for (Taclet t : taclets) {
            b = taclet2Builder.get(t);
            if(t.getChoices().subset(activatedChoices)){
                if(b!=null && b.getGoal2Choices()!=null){
                    t = b.getTacletWithoutInactiveGoalTemplates(
                            activatedChoices);
                }
                if(t!=null){
                    result = result.add(t);
                }
            }
        }
        return result;
    }


    /** returns the built-in rules of this initial configuration
     */
    public ImmutableList<BuiltInRule> builtInRules() {
        Profile profile = getProfile();
        return (profile == null
        	? ImmutableSLList.<BuiltInRule>nil()
        	: profile.getStandardRules().getStandardBuiltInRules());
    }


    /** returns a newly created taclet index for the set of activated
     * taclets contained in this initial configuration
     */
    public TacletIndex createTacletIndex() {
        return new TacletIndex(activatedTaclets());
    }


    /**
     * returns a new created index for built in rules (at the moment immutable
     * list)
     */
    public BuiltInRuleIndex createBuiltInRuleIndex() {
        return new BuiltInRuleIndex(builtInRules());
    }


    /**
     * returns the namespaces of this initial configuration
     */
    public NamespaceSet namespaces() {
        return services.getNamespaces();
    }


    /** returns the function namespace of this initial configuration
     */
    public Namespace funcNS() {
        return namespaces().functions();
    }


    /** returns the sort namespace of this initial configuration
     */
    public Namespace sortNS() {
        return namespaces().sorts();
    }


    /** returns the heuristics namespace of this initial configuration
     */
    public Namespace ruleSetNS() {
        return namespaces().ruleSets();
    }


    /** returns the variable namespace of this initial configuration
     */
    public Namespace varNS() {
        return namespaces().variables();
    }


    /** returns the program variable namespace of this initial configuration
     */
    public Namespace progVarNS() {
        return namespaces().programVariables();
    }


    /** returns the choice namespace of this initial configuration
     */
    public Namespace choiceNS() {
        return namespaces().choices();
    }

    
    public void setSettings(ProofSettings settings) {
	  this.settings = settings;
	  for(LDT ldt : getServices().getTypeConverter().getModels()) {
		ldt.proofSettingsUpdated(settings);
	  }
	  // replace the <inv> symbol as it may have changed arity
	  namespaces().functions().add(services.getJavaInfo().getInv());
	}
    
    
    public ProofSettings getSettings() {
	return settings;
    }


    /** returns a copy of this initial configuration copying the namespaces,
     * the contained JavaInfo while using the immutable set of taclets in the
     * copy
     */
    @SuppressWarnings("unchecked")
    public InitConfig copy() {
        InitConfig ic = new InitConfig(services.copyPreservesLDTInformation());
        ic.setActivatedChoices(activatedChoices);
        ic.category2DefaultChoice = ((HashMap<String,String>) category2DefaultChoice.clone());
        ic.setTaclet2Builder(
                (HashMap<Taclet, TacletBuilder>) taclet2Builder.clone());
        ic.setTaclets(taclets);
        ic.originalKeYFileName = originalKeYFileName;
        return ic;
    }
    
    

    /** returns a copy of this initial configuration copying the namespaces,
     * the contained JavaInfo while using the immutable set of taclets in the
     * copy
     */
    @SuppressWarnings("unchecked")
    public InitConfig deepCopy() {
        InitConfig ic = new InitConfig(services.copy());
        ic.setActivatedChoices(activatedChoices);
        ic.category2DefaultChoice = ((HashMap<String,String>) category2DefaultChoice.clone());
        ic.setTaclet2Builder(
                (HashMap<Taclet, TacletBuilder>) taclet2Builder.clone());
        ic.setTaclets(taclets);
        ic.originalKeYFileName = originalKeYFileName;
        return ic;
    }

    public String toString() {
        return
            "Namespaces:" + namespaces() +"\n" +
            "Services:" + services +"\n"+
            "Taclets:" + getTaclets() +"\n"+
            "Built-In:" + builtInRules() +"\n";
    }
}
