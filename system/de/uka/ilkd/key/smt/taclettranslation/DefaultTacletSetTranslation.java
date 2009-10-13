package de.uka.ilkd.key.smt.taclettranslation;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;

public class DefaultTacletSetTranslation implements TacletSetTranslation {

    /**
     * if <code>translate</code> is <code>true</code> the method <code>getTranslation()</code> will first translate the given taclets before it returns <code>translation</code>.
    */
    private boolean translate = false;
    
    /**
     * Translation of the taclets stored in <code>taclets</code>.
     * 
     * */
    private ImmutableList<TacletFormula> translation = ImmutableSLList.nil();
    
    /**
     * Taclets can not be translated because checking the taclet failed.
     */
    private ImmutableList<TacletFormula> notTranslated = ImmutableSLList.nil();
    
    /**
     * List of taclets that should be translated. The translation will be done by calling <code>getTtranslation()</code>.
     */
    private ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();
    
    /**
     * List of taclet translators. If you want to add translators use <code>add</code>.
     * When a taclet is translated the first translator in the list is chosen which fits the taclet.
     */
    private ImmutableList<TacletTranslator>  translators = ImmutableSLList.nil(); 
    
    /**
     * List of used heuristics. Use <code>add</code> and <code>remove</code> to change the list.
     */
    private ImmutableList<String> heuristics = ImmutableSLList.nil();
    

    
    public DefaultTacletSetTranslation(){
	translators = translators.append(new RewriteTacletTranslator());
    }
    
    /**
     * Checks whether the given taclet contains at least one heuristic of the list <code>heuristics</code>.
     * @param t taclet to be checked.
     * @return  <code>true</code> if the taclet contains one of the given heuristic otherwise <code>false</code>.
     */
    public boolean checkHeuristic(Taclet t){
	for(String h : heuristics){
	    for(RuleSet rs : t.getRuleSets()){
		if(rs.name().toString().equals(h)) return true; 
	    }
	  
	}
	return false;
    }
   
    
    public ImmutableList<TacletFormula> getTranslation() {
	
	// only translate once a time. 
	if(!translate) return translation;
	translate = false;
	
	notTranslated = ImmutableSLList.nil();
	translation = ImmutableSLList.nil();
	
	
	for(Taclet t : taclets){
	   if(!heuristics.isEmpty() && !checkHeuristic(t)){
	       
	       notTranslated = notTranslated.append(new DefaultTacletFormula(t,null,"The taclet does not have the right heuristic."));
	       continue;
	   }
	   for(TacletTranslator translator: translators){
	       try
	       { // check for the right translator
		   
		   Term term = translator.translate(t);		  
		   translation = translation.append(new DefaultTacletFormula(t,term,""));
		   break; // translate only once a time.
	       }catch(IllegalTacletException e){
		   
		   notTranslated = notTranslated.append(new DefaultTacletFormula(t,null,e.getMessage()));
		  
	       }
	   }
	}
	
	return translation;
    }

   
    public void setTacletSet(ImmutableSet<Taclet> set) {
	translate = true;
	translation = ImmutableSLList.nil();
	taclets = set;

    }


    public ImmutableList<TacletFormula> getNotTranslated() {

	return notTranslated;
    }


    public void addHeuristic(String h) {
	heuristics=heuristics.append(h);
	
    }


    public boolean removeHeursitic(String h) {
	int size = heuristics.size();
	heuristics = heuristics.removeFirst(h);
	return size == heuristics.size()+1;
    }


    public void update() {
	translate = true;
	getTranslation();
	
    }




}
