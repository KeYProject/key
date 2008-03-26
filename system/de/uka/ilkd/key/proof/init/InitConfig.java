// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.NoSuchElementException;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.*;

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
       
    private final Profile profile;
    
    /**
     * the proof environment this init config belongs to
     */
    private final ProofEnvironment env;

    
    private SetOfTaclet taclets = SetAsListOfTaclet.EMPTY_SET;
       
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
    private SetOfChoice activatedChoices = SetAsListOfChoice.EMPTY_SET;
    
    /** HashMap for quick lookups taclet name->taclet */
    private HashMap<Name, Named> quickTacletMap;
    
    private String originalKeYFileName;
    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public InitConfig(Services services, Profile profile) {
	this.services  = services;
	this.profile   = profile; 
	this.env       = new ProofEnvironment(this);
	
        sortNS().add(Sort.NULL);
        funcNS().add(Op.NULL);
        category2DefaultChoice = ProofSettings.DEFAULT_SETTINGS.
            getChoiceSettings().getDefaultChoices();
    }

    
    public InitConfig() {
        this(new Services(), null);
    }
    
           
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Helper for add().
     */
    private void addSorts (NamespaceSet ns, ModStrategy mod) {
        final IteratorOfNamed sortsIt = ns.sorts ().elements ().iterator ();
        while ( sortsIt.hasNext () ) {
            final Named named = sortsIt.next ();
            if ( named instanceof GenericSort ) {
                if ( mod.modifyGenericSorts () ) sortNS ().add ( named );
            } else {
                if ( mod.modifySorts () ) sortNS ().add ( named );
            }
        }
    }
    
    
    
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
	return profile;
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
    public void addCategory2DefaultChoices(HashMap<String,String> init){
        boolean changed = false;
        for (final Map.Entry<String, String> entry : init.entrySet()) {
            if(!category2DefaultChoice.containsKey(entry.getKey())){
                changed=true;
                category2DefaultChoice.put(entry.getKey(), entry.getValue());
            }
        }
        if(changed){
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().
                setDefaultChoices((HashMap<String, String>)category2DefaultChoice.clone());
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
    public void setActivatedChoices(SetOfChoice activatedChoices) {
        category2DefaultChoice = 
	    ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().
	    getDefaultChoices();

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
    public SetOfChoice getActivatedChoices(){
        return activatedChoices;
    }

        
    public void setTaclets(SetOfTaclet taclets){
        this.taclets = taclets;
    }
    
    
    public SetOfTaclet getTaclets(){
        return taclets;
    }
    
    
    public Taclet lookupActiveTaclet(Name name) {
	if (quickTacletMap == null) {
            quickTacletMap = new HashMap<Name, Named>();
            IteratorOfTaclet it = activatedTaclets().iterator();
            while (it.hasNext())  {
                Taclet t = it.next();
                quickTacletMap.put(t.name(), t);
                IteratorOfName itOld = t.oldNames().iterator();
                while (itOld.hasNext()) {
                    quickTacletMap.put(itOld.next(), t);
                }
            }
        }
	
        return (Taclet) quickTacletMap.get(name);
    }

    
    /**
     * returns the activated taclets of this initial configuration
     */
    public SetOfTaclet activatedTaclets() {
        SetOfTaclet result = SetAsListOfTaclet.EMPTY_SET;
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
    public ListOfBuiltInRule builtInRules() {
        return (profile == null 
        	? SLListOfBuiltInRule.EMPTY_LIST 
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

    
    public void createNamespacesForActivatedChoices(){
        IteratorOfChoice it = activatedChoices.iterator();
        while(it.hasNext()){
	    Choice c = it.next();
            funcNS().add(c.funcNS());
        }
    }

    
    public ProofSettings mergedProofSettings() {
        ProofSettings defaultSettings = ProofSettings.DEFAULT_SETTINGS;
        ProofAggregate someProof = null;
	try {
            someProof = ((ProofAggregate)getProofEnv().getProofs().iterator().next());
	}catch(NoSuchElementException ne){
	    throw new RuntimeException(ne);
	}
        if (someProof!=null) {
            return defaultSettings.setChoiceSettings(
                someProof.getFirstProof().getSettings().getChoiceSettings());
        } else {
            return defaultSettings;
        }
    }

    
    /** adds namespaces to the namespaces of this initial configuration
     */
    public void add(NamespaceSet ns, ModStrategy mod) {
        if (mod.modifyFunctions()) funcNS().add(ns.functions());
        addSorts ( ns, mod );
        if (mod.modifyVariables()) varNS().add(ns.variables());
        if (mod.modifyProgramVariables()) progVarNS().add(ns.programVariables());
        if (mod.modifyHeuristics()) ruleSetNS().add(ns.ruleSets());
        if (mod.modifyChoices()) choiceNS().add(ns.choices());
    }
    
    
    public void setOriginalKeYFileName(String name) {
        originalKeYFileName = name;
    }
    
    
    public String getOriginalKeYFileName() {
        return originalKeYFileName;
    }

   
    
    /** returns a copy of this initial configuration copying the namespaces,
     * the contained JavaInfo while using the immutable set of taclets in the
     * copy
     */
    public InitConfig copy() {
        InitConfig ic = new InitConfig(services.copyPreservesLDTInformation(), 
        			       profile);
        ic.setActivatedChoices(activatedChoices);
        ic.category2DefaultChoice = ((HashMap) category2DefaultChoice.clone());
        ic.setTaclet2Builder((HashMap<Taclet, TacletBuilder>) taclet2Builder.clone());
        ic.setTaclets(taclets);
        ic.originalKeYFileName = originalKeYFileName;
        return ic;
    }

    
    /**
     * toString
     */
    public String toString() {
        return
            "Namespaces:" + namespaces() +"\n" +
            "Services:" + services +"\n"+
            "Taclets:" + getTaclets() +"\n"+
            "Built-In:" + builtInRules() +"\n";
    }
}
