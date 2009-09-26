package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;

public class DefaultTacletSetTranslation implements TacletSetTranslation {

    /**
     * if <code>translate</code> is <code>true</code> the method <code>getTranslation()</code> will first translate the given taclets before it returns <code>translation</code>.
    */
    private boolean translate = false;
    
    /**
     * Translation of the taclets stored in <code>taclets</code>
     * 
     * */
    private ImmutableList<TacletFormula> translation = ImmutableSLList.nil();
    
    /**
     * List of taclets that should be translated. The translation will be done by calling <code>getTtranslation()</code>.
     */
    private ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();
    
    /**
     * List of taclet translators. If you want to add translators use <code>add</code>.
     * When a taclet is being translated the first translator in the list is chosen which fits the taclet.
     */
    private ImmutableList<TacletTranslator>  translators = ImmutableSLList.nil(); 
    

    
    public DefaultTacletSetTranslation(){
	translators = translators.append(new RewriteTacletTranslator());
    }
   
    
    public ImmutableList<TacletFormula> getTranslation() {
	// there is no translation without taclets.
	if(taclets.isEmpty()){
	    translation = ImmutableSLList.nil();
	}
	// only translate once a time. 
	if(!translate) return translation;
	translate = false;
	
	translation = ImmutableSLList.nil();
	
	
	for(Taclet t : taclets){
	   for(TacletTranslator translator: translators){
	       String res = translator.check(t);
	       if(res == TacletTranslator.RIGHT){ // check for the right translator
		   System.out.println(t.getClass().getName());
		   Term term = translator.translate(t);
		  
		   translation = translation.append(new DefaultTacletFormula(t,term));
		   break; // translate only once a time.
	       }else{
		   System.out.println(res);
		   System.out.println(t.toString());
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




}
