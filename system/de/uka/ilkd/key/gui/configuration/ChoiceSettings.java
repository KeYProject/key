// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.configuration;

import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.logic.*;

public class ChoiceSettings implements Settings {

    private static final String DEFAULTCHOICES_KEY = "[Choice]DefaultChoices";
    private static final String CHOICES_KEY = "[Choice]Choices";
    private LinkedList listenerList = new LinkedList();
    private HashMap category2Default;
    /** maps categories to a set of Strings(representing the choices
     * which are options for this category).*/
    private HashMap category2Choices=new HashMap();


    public ChoiceSettings() {
	category2Default = new HashMap();
    }

    public ChoiceSettings(HashMap category2Default){
	this.category2Default = category2Default;
    }

    public void setDefaultChoices(HashMap category2Default){
	HashMap category2Defaultold = this.category2Default;
	this.category2Default = category2Default;
	if(category2Defaultold!=null && 
	   !category2Defaultold.equals(category2Default)){
	    fireSettingsChanged();
	}
    }

    /** returns a copy of the HashMap that maps categories to 
     * their choices. */ 
    public HashMap getChoices(){
        return (HashMap) category2Choices.clone();
    }

    
    /** returns a copy of the HashMap that maps categories to 
     * their default choices. */ 
    public HashMap getDefaultChoices(){
	return (HashMap) category2Default.clone();
    }
    /** 
     * returns the current selected choices as set    
     */ 
    public SetOfChoice getDefaultChoicesAsSet() {              
        return choiceMap2choiceSet(category2Default);   
    }

    private SetOfChoice choiceMap2choiceSet(HashMap ccc) {
        final Iterator choiceIter = ccc.entrySet().iterator();
        SetOfChoice choices = SetAsListOfChoice.EMPTY_SET;        
        while (choiceIter.hasNext()) {
            final Map.Entry entry = (Entry) choiceIter.next();
            choices = choices.
              add(new Choice(new Name(entry.getValue().toString()), 
                    entry.getKey().toString()));
        }
        return choices;
    }
    
    /** updates <code>category2Choices</code> if new entries are found
     * in <code>choiceNS</code> or if entries of <code>category2Choices</code>
     * are no longer present in <code>choiceNS</code>
     * @param remove remove entries not present in <code>choiceNS</code> */
    public void updateChoices(Namespace choiceNS, boolean remove){
	IteratorOfNamed it = choiceNS.allElements().iterator();
	HashMap c2C = new HashMap();
	Choice c;
	Set soc;
	while(it.hasNext()){
	    c=(Choice)it.next();
	    if(c2C.containsKey(c.category())){
		soc=(Set) c2C.get(c.category().toString());
		soc.add(c.name().toString());
		c2C.put(c.category(),soc);
	    }else{
		soc = new HashSet();
		soc.add(c.name().toString());
		c2C.put(c.category(),soc);
	    }
	}
	if(!c2C.equals(category2Choices)){
	    if(remove){
		category2Choices = c2C;
		fireSettingsChanged();
	    }else{
		category2Choices.putAll(c2C);
		ProofSettings.DEFAULT_SETTINGS.saveSettings();
	    }
	}
	Iterator catIt = getDefaultChoices().keySet().iterator();
	while(catIt.hasNext()){
	    String s = (String) catIt.next();
	    if(category2Choices.containsKey(s)){
		if(!((Set)category2Choices.get(s)).
		   contains(category2Default.get(s))){
		    category2Default.put(s,((Set)category2Choices.get(s)).
					 iterator().next());
		    fireSettingsChanged();
		}
	    }else{
		category2Default.remove(s);
		fireSettingsChanged();
	    }
	}
    }


    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
	Iterator it = listenerList.iterator();
	ProofSettings.DEFAULT_SETTINGS.saveSettings();
	while (it.hasNext()) {
	    ((SettingsListener)it.next()).settingsChanged(new GUIEvent(this));
	}
    }

    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
	String choiceSequence = props.getProperty(DEFAULTCHOICES_KEY);
	// set choices
	if (choiceSequence != null) {
	    StringTokenizer st = new StringTokenizer(choiceSequence, ",");
	    while (st.hasMoreTokens()) {
		StringTokenizer st2 = new StringTokenizer(
				       st.nextToken().trim(), "-");
		String category = st2.nextToken().trim();
		String def = st2.nextToken().trim();
		category2Default.put(category, def);
		
	    }
	}
	choiceSequence = props.getProperty(CHOICES_KEY);
	if (choiceSequence != null) {
	    StringTokenizer st = new StringTokenizer(choiceSequence, ",");
	    while (st.hasMoreTokens()) {
		StringTokenizer st2 = new StringTokenizer(
				       st.nextToken().trim(), "-");
		String category = st2.nextToken().trim();
		Set soc = new HashSet();
		while(st2.hasMoreTokens()){
		    soc.add(st2.nextToken().trim());
		}
		category2Choices.put(category, soc);
	    }
	}
    }

    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of 
     * the form &lt; key &gt; = &lt; value &gt; (,&lt; value &gt;)* are allowed.
     * @param props the Properties object where to write the 
     * settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
	Map.Entry entry;
	String choiceSequence = "";
	Iterator it = category2Default.entrySet().iterator();
	while(it.hasNext()) {
	    entry = (Map.Entry)it.next();
	    choiceSequence += entry.getKey().toString()+"-"+
		entry.getValue().toString();
	    if(it.hasNext()){
		choiceSequence += " , ";
	    }
	}
	props.setProperty(DEFAULTCHOICES_KEY, choiceSequence);
	choiceSequence = "";
	it = category2Choices.keySet().iterator();
	while(it.hasNext()){
	    String cat = (String)it.next();
	    Set soc = (Set)category2Choices.get(cat);
	    choiceSequence += cat;
	    Iterator it2 = soc.iterator();
	    while(it2.hasNext()){
		choiceSequence += "-"+it2.next().toString();
	    }
	    if(it.hasNext()){
		choiceSequence += " , ";
	    }
	}
	props.setProperty(CHOICES_KEY, choiceSequence);	
    }
    
    public ChoiceSettings updateWith(SetOfChoice sc) {
        IteratorOfChoice it = sc.iterator();
        while (it.hasNext()) {
            Choice c = it.next();
            if (category2Default.containsKey(c.category())) {
                category2Default.remove(c.category());
            }
            category2Default.put(c.category(), c.name().toString());
        }
        return this;
    }
    


    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
	listenerList.add(l);
    }
}
