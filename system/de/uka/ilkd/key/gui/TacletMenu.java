// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.*;

import javax.swing.*;

import org.apache.log4j.Logger;

import de.uka.ilkd.hoare.gui.HoareLoopInvRuleMenuItem;
import de.uka.ilkd.hoare.rule.HoareLoopInvariantRule;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IteratorOfSchemaVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.*;

/**
 *  This class creates a menu with Taclets as entries. The invoker has
 * to be of type SequentView because of the method call selectedTaclet
 * that hands over the selected Taclet. The class is used to get all
 * Taclet that are applicable at a selected position in a sequent.
 */ 
class TacletMenu extends JMenu {

    private PosInSequent pos;
    private SequentView sequentView;
    private KeYMediator mediator;

    private TacletAppComparator comp = new TacletAppComparator();
    
    static Logger logger = Logger.getLogger(TacletMenu.class.getName());
    
    /** 
     * creates empty menu 
     */
    TacletMenu() {}


    /** creates a new menu that displays all applicable rules at the given
     * position
     * @param sequentView the SequentView that is the parent of this menu
     * @param findList ListOfTaclet with all applicable FindTaclets
     * @param rewriteList ListOfTaclet with all applicable RewriteTaclets
     * @param noFindList ListOfTaclet with all applicable noFindTaclets
     * @param builtInList ListOfBuiltInRule with all applicable BuiltInRules
     * @param pos the PosInSequent
     */ 
    TacletMenu(SequentView sequentView,
	       ListOfTacletApp findList, ListOfTacletApp rewriteList,
	       ListOfTacletApp noFindList, ListOfBuiltInRule builtInList,
	       PosInSequent pos) {
        super();        
	this.sequentView = sequentView;
	this.mediator = sequentView.mediator();
 	this.pos = pos;
	// delete RewriteTaclet from findList because they will be in
	// the rewrite list and concatenate both lists
	createTacletMenu(removeRewrites(findList).prepend(rewriteList),
			 noFindList, builtInList, new MenuControl());
    }

    
    /** removes RewriteTaclet from list
     * @param list the ListOfTaclet from where the RewriteTaclet are
     * removed
     * @return list without RewriteTaclets
     */
    private ListOfTacletApp removeRewrites(ListOfTacletApp list) {
	ListOfTacletApp result = SLListOfTacletApp.EMPTY_LIST;
	IteratorOfTacletApp it = list.iterator();

	while(it.hasNext()) {
	    TacletApp tacletApp = it.next();
	    Taclet taclet=tacletApp.taclet();
	    result = (taclet instanceof RewriteTaclet ? result :
		      result.prepend(tacletApp));
	}
	return result;
    }


    /** creates the menu by adding all submenus and items */
    private void createTacletMenu(ListOfTacletApp find,
				  ListOfTacletApp noFind,
				  ListOfBuiltInRule builtInList,
				  MenuControl control) {	 
	addActionListener(control);
	boolean rulesAvailable=(addSection("Find", sort(find), control));
	if (pos != null && pos.isSequent()) {
	    rulesAvailable=addSection("NoFind", noFind, control)
		| rulesAvailable;
	}
	if (!rulesAvailable) {
	    createSection("No rules applicable.");
	}

	createBuiltInRuleMenu(builtInList, control);
        
	createFocussedAutoModeMenu ( control );
    
	//        addPopFrameItem(control);

	addClipboardItem(control);

	if (pos != null) {
	    PosInOccurrence occ = pos.getPosInOccurrence();	    
	    if (occ != null && occ.posInTerm() != null) {
		Term t = occ.subTerm ();
		createAbbrevSection(t, control);

		if(t.op() instanceof ProgramVariable) {
		    ProgramVariable var = (ProgramVariable)t.op();
		    if(var.getProgramElementName().getCreationInfo() != null) {
		    	createNameCreationInfoSection(control);
		    }
		}
	    }
	}
    }

    private void createBuiltInRuleMenu(ListOfBuiltInRule builtInList,
				       MenuControl            control) {

	if (builtInList != SLListOfBuiltInRule.EMPTY_LIST) {
	    addSeparator();	
	    IteratorOfBuiltInRule it = builtInList.iterator();
	    while (it.hasNext()) {                
		addBuiltInRuleItem(it.next(), control);
	    }
	}
    }
				      
    /**
     * adds an item for built in rules (e.g. Run Simplify or Update Simplifier)
     */
    private void addBuiltInRuleItem(BuiltInRule builtInRule,
				    MenuControl control) {
        final JMenuItem item;
        if (builtInRule instanceof UseMethodContractRule) {
            item = new UseMethodContractRuleItem(mediator.mainFrame(),
                                                 (UseMethodContractRule)builtInRule,
                                                 mediator.getSelectedProof(), 
                                                 pos.getPosInOccurrence());           
        } else if (builtInRule instanceof HoareLoopInvariantRule) { 
            item = new HoareLoopInvRuleMenuItem(pos.getPosInOccurrence(),
                    mediator.getSelectedGoal());
        } else {
            item = new DefaultBuiltInRuleMenuItem(builtInRule);                       
        }
        item.addActionListener(control);
        add(item);
    }

    
    private void createFocussedAutoModeMenu (MenuControl control) {
        addSeparator();
        JMenuItem item = new FocussedRuleApplicationMenuItem ();
        item.addActionListener(control);
        add(item);        
    }
    

    private ListOfTacletApp sort(ListOfTacletApp finds) {
	ListOfTacletApp result = SLListOfTacletApp.EMPTY_LIST;
	List list = new ArrayList(finds.size());

	IteratorOfTacletApp it = finds.iterator();
	while (it.hasNext()) {
	    list.add(it.next());
	}

	Collections.sort(list, comp);

	Iterator it2 = list.iterator();
	while (it2.hasNext()) {
	    result = result.prepend((TacletApp)it2.next());
	}

	return result;
    }


    private void createAbbrevSection(Term t, MenuControl control){
	AbbrevMap scm = mediator.getNotationInfo().getAbbrevMap();
	JMenuItem sc = null;
	if(scm.containsTerm(t)){
	    sc = new JMenuItem("Change abbreviation");
	    sc.addActionListener(control);
	    add(sc);
	    if(scm.isEnabled(t)){
		sc = new JMenuItem("Disable abbreviation");
	    }else{
		sc = new JMenuItem("Enable abbreviation");
	    }
	}else{
	    sc = new JMenuItem("Create abbreviation");
	}
	sc.addActionListener(control);
	add(sc);
    }


    private void createNameCreationInfoSection(MenuControl control) {
	JMenuItem item = new JMenuItem("View name creation info...");
	item.addActionListener(control);
	add(item);
    }



    /** creates a non selectable label with the specified name and adds it to
     * the component followed by the entries of this section 
     * @param title a String the title of the section
     * @param taclet ListOfTaclet that contains the Taclets belonging to this section
     * @return true if section has been added (empty sections are not added)
     */ 
    private boolean addSection(String title, ListOfTacletApp taclet, 
			       MenuControl control) {
	if (taclet.size() > 0) {
	    //uncomment if you want submenus with subtitels
	    //	    insert(createSubMenu(taclet, title, control), 1);
	    //	    createSection(title);
	    add(createMenuItems(taclet, control));
	    return true;
	}
	return false;
    }

    /** inserts separator followed from the section's title 
     * @param title a String that contains the title of the section
     */
    private void createSection(String title) {
	//addSeparator();
	add(new JLabel(title));
    }
    

    private void addPopFrameItem(MenuControl control) {
	JMenuItem item = new JMenuItem("Pop method frame");
	item.addActionListener(control);
	add(item);
    }

    
    private void addClipboardItem(MenuControl control) {
	addSeparator();
	JMenuItem item = new JMenuItem("to clipboard");
	item.addActionListener(control);
	add(item);
    }
    


    /** adds array of TacletMenuItem to itself*/
    private void add(TacletMenuItem[] items) {
	for (int i = 0; i < items.length; i++) {
	    add((Component) items[i]);
	}
    }

    /** creates new TacletMenuItems for each taclet in the list and set
     * the given MenuControl as their ActionListener
     * @param taclets ListOfTaclet with the Taclets the items represent
     * @param control the ActionListener
     * @return the new MenuItems
     */
    private TacletMenuItem[] createMenuItems(ListOfTacletApp taclets, 
					     MenuControl  control) {
	List items = new LinkedList();
	IteratorOfTacletApp it = taclets.iterator();
	
        final InsertHiddenTacletMenuItem insHiddenItem = 
            new InsertHiddenTacletMenuItem(mediator.mainFrame(), 
                    mediator.getNotationInfo(), mediator.getServices());
        
        final InsertionTacletBrowserMenuItem insSystemInvItem = 
            new InsertSystemInvariantTacletMenuItem(mediator.mainFrame(), 
                    mediator.getNotationInfo(), mediator.getServices());
       
        
        for (int i = 0; it.hasNext(); i++) {
            final TacletApp app = it.next();
           
            final Taclet taclet = app.taclet();
            if (insHiddenItem.isResponsible(taclet)) {
                insHiddenItem.add(app);
            } else if (insSystemInvItem.isResponsible(taclet)) { 
                insSystemInvItem.add(app);
            } else {
                final TacletMenuItem item = 
                    new DefaultTacletMenuItem(this, app, 
                        mediator.getNotationInfo()); 
                item.addActionListener(control);
                items.add(item);                
            }        
	}
        
        if (insHiddenItem.getAppSize() > 0) {
            items.add(0, insHiddenItem);
            insHiddenItem.addActionListener(control);
        }
        
        if (insSystemInvItem.getAppSize() > 0) {
            items.add(0, insSystemInvItem);
            insSystemInvItem.addActionListener(control);
        }
        
	return (TacletMenuItem[])
            items.toArray(new TacletMenuItem[items.size()]);
    }
        
    /** makes submenus invisible */
    void invisible() {
	for (int i = 0; i < getMenuComponentCount(); i++) {
	    if (getMenuComponent(i) instanceof JMenu) 
		((JMenu)getMenuComponent(i)).getPopupMenu().setVisible(false);
	}
    }
    
    /** ActionListener */
    class MenuControl implements ActionListener{

	private boolean validabbreviation(String s){
	    if(s==null || s.length()==0) return false;
	    for(int i=0; i<s.length(); i++){
		if(!((s.charAt(i)<='9' && s.charAt(i)>='0')||
		     (s.charAt(i)<='z' && s.charAt(i)>='a')||
		     (s.charAt(i)<='Z' && s.charAt(i)>='A')||
		     s.charAt(i)=='_')) return false;
	    }
	    return true;
	}

	public void actionPerformed(ActionEvent e) {
	    if (e.getSource() instanceof TacletMenuItem) {
		((SequentView)(getPopupMenu().getInvoker()))
		    .selectedTaclet(((TacletMenuItem) e.getSource()).connectedTo(), 
				    pos);
            } else if (e.getSource() instanceof UseMethodContractRuleItem) {
                mediator.selectedUseMethodContractRule
                    (((UseMethodContractRuleItem) e.getSource()).getRuleApp());   
            } else if (e.getSource() instanceof HoareLoopInvRuleMenuItem) {
                mediator.selectedHoareLoopInvRule
                (((HoareLoopInvRuleMenuItem) e.getSource()).getRuleApp());   
            }  else if (e.getSource() instanceof BuiltInRuleMenuItem) {
                        mediator.selectedBuiltInRule
                    (((BuiltInRuleMenuItem) e.getSource()).connectedTo(), 
                     pos.getPosInOccurrence());
	    } else if (e.getSource() instanceof FocussedRuleApplicationMenuItem) {
	        mediator.getInteractiveProver ()
	            .startFocussedAutoMode ( pos.getPosInOccurrence (),
	                                     mediator.getSelectedGoal () );
	    } else {
		if (((JMenuItem)e.getSource()).getText()
		    .startsWith("to clipboard")){
                    Main.copyHighlightToClipboard(sequentView);
		} else if(((JMenuItem)e.getSource()).getText().
			  startsWith("Pop method frame")){
		    //                        mediator.popMethodFrame();
		} else if(((JMenuItem)e.getSource()).getText().
			  startsWith("Disable abbreviation")){
		    PosInOccurrence occ = pos.getPosInOccurrence();	    
		    if (occ != null && occ.posInTerm() != null) {
			mediator.getNotationInfo().getAbbrevMap().setEnabled(occ.subTerm(),false);
			sequentView.printSequent();
		    }
		}else if(((JMenuItem)e.getSource()).getText().
			 startsWith("Enable abbreviation")){
		    PosInOccurrence occ = pos.getPosInOccurrence();	    
		    if (occ != null && occ.posInTerm() != null) {
			mediator.getNotationInfo().
			    getAbbrevMap().setEnabled(occ.subTerm(),true);
			sequentView.printSequent();
		    }
		}else if(((JMenuItem)e.getSource()).getText().
			 startsWith("Create abbreviation")){
		    PosInOccurrence occ = pos.getPosInOccurrence();
		    if (occ != null && occ.posInTerm() != null) {
			String abbreviation = (String)JOptionPane.showInputDialog
			    (new JFrame(),
			     "Enter abbreviation for term: \n"+occ.subTerm().toString(), 
			     "New Abbreviation",
			     JOptionPane.QUESTION_MESSAGE,
			     null,
			     null,
			     "");
				    
			try{
			    if(abbreviation!=null){
				if(!validabbreviation(abbreviation)){
				    JOptionPane.showMessageDialog(new JFrame(),
								  "Only letters, numbers and '_' are allowed for Abbreviations", 
								  "Sorry",
								  JOptionPane.INFORMATION_MESSAGE);
				}else{
				    mediator.getNotationInfo().
					getAbbrevMap().put(occ.subTerm(),abbreviation,true);
				    sequentView.printSequent();
				}
			    }
			}catch(AbbrevException sce){
			    JOptionPane.showMessageDialog(new JFrame(), sce.getMessage(), "Sorry",
							  JOptionPane.INFORMATION_MESSAGE);
			}
		    }

		}else if(((JMenuItem)e.getSource()).getText().
			 startsWith("Change abbreviation")){
		    PosInOccurrence occ = pos.getPosInOccurrence();
		    if (occ != null && occ.posInTerm() != null) {
			String abbreviation = (String)JOptionPane.showInputDialog
			    (new JFrame(),
			     "Enter abbreviation for term: \n"+occ.subTerm().toString(),
			     "Change Abbreviation",
			     JOptionPane.QUESTION_MESSAGE,
			     null,
			     null,
			     mediator.getNotationInfo().
			     getAbbrevMap().getAbbrev(occ.subTerm()).substring(1));
			try{
			    if(abbreviation!=null){
				if(!validabbreviation(abbreviation)){
				    JOptionPane.showMessageDialog(new JFrame(),
								  "Only letters, numbers and '_' are allowed for Abbreviations",
								  "Sorry",
								  JOptionPane.INFORMATION_MESSAGE);
				}else{
				    mediator.getNotationInfo().
					getAbbrevMap().changeAbbrev(occ.subTerm(),abbreviation);
				    sequentView.printSequent();
				}
			    }
			}catch(AbbrevException sce){
			    JOptionPane.showMessageDialog(new JFrame(), sce.getMessage(), "Sorry",
							  JOptionPane.INFORMATION_MESSAGE);
			}
		    }
		} else if(((JMenuItem)e.getSource()).getText().
			 startsWith("View name creation info")) {
		    Term t = pos.getPosInOccurrence().subTerm();
		    ProgramVariable var = (ProgramVariable)t.op();
		    ProgramElementName name = var.getProgramElementName();
		    NameCreationInfo info = name.getCreationInfo();
		    String message;
		    if(info != null) {
			message = info.infoAsString();
		    } else {
		        message = "No information available.";
		    }
		    JOptionPane.showMessageDialog(null,
		    				  message,
						  "Name creation info",
		  				  JOptionPane.INFORMATION_MESSAGE);
		}
	    }
	}
    }



    static class FocussedRuleApplicationMenuItem extends JMenuItem {
        public FocussedRuleApplicationMenuItem () {
            super("Apply rules automatically here");
            setToolTipText("<html>Initiates and restricts automatic rule applications on the " +
                        "highlighted formula, term or sequent.<br> "+
                        "'Shift + left mouse click' on the highlighted " +
                        "entity does the same.</html>");
        }
               
    }
    
    
    static class TacletAppComparator implements Comparator {

	private int countFormulaSV(TacletSchemaVariableCollector c) {
	    int formulaSV = 0;
	    IteratorOfSchemaVariable it = c.varIterator();
	    while (it.hasNext()) {
		SchemaVariable sv = it.next();
		if(sv instanceof SortedSchemaVariable) {
		    if (((SortedSchemaVariable)sv).sort() == Sort.FORMULA) {
			formulaSV++;
		    }
		}
	    }
	
	    return formulaSV;
	}
	
	/** this is a rough estimation about the goal complexity. The
	 * complexity depends on the depth of the term to be replaced.
	 * If no such term exists we add a constant (may be refined in
	 * future)
	 */
	private int measureGoalComplexity(ListOfTacletGoalTemplate l) {
	    int result = 0;
	    IteratorOfTacletGoalTemplate it = l.iterator();
	    while (it.hasNext()) {
		TacletGoalTemplate gt = it.next();
		if (gt instanceof RewriteTacletGoalTemplate) {
		    if (((RewriteTacletGoalTemplate)gt).replaceWith() != null) {
			result += ((RewriteTacletGoalTemplate)gt).replaceWith().depth();
		    }
		} 
		if (gt.sequent() != Sequent.EMPTY_SEQUENT) {
		    result += 10;
		}
	    }
	    return result;
	}
	
	
	/**
	 * rough approximation of the program complexity
	 */
	public int programComplexity(JavaBlock b) {
	    if (b == JavaBlock.EMPTY_JAVABLOCK) {
		return 0;
	    }
	    return new de.uka.ilkd.key.java.visitor.JavaASTWalker(b.program()) { 
		    private int counter = 0;
			    
		    protected void doAction(ProgramElement pe) {                      
                        counter++;
		    }		
                    
		    public int getCounter() {
			counter = 0;
			start();
			return counter;
		    }
		}.getCounter();
	}
	
	public int compare(Object o1, Object o2) {
	    FindTaclet taclet1 = (FindTaclet)(((TacletApp)o1).taclet());
	    FindTaclet taclet2 = (FindTaclet)(((TacletApp)o2).taclet());
		    
	    int findComplexity1 = taclet1.find().depth();
	    int findComplexity2 = taclet2.find().depth();
	    findComplexity1 += programComplexity(taclet1.find().javaBlock());
	    findComplexity2 += programComplexity(taclet2.find().javaBlock());
	
	    if ( findComplexity1 < findComplexity2 ) {
		return -1;
	    } else if (findComplexity1 > findComplexity2) {
		return 1;
	    }		    		    		    
	
	    // depth are equal. Number of schemavariables decides
	    TacletSchemaVariableCollector coll1 = new TacletSchemaVariableCollector();
	    taclet1.find().execPostOrder(coll1);
	    int formulaSV1 = countFormulaSV(coll1);
		    
	    TacletSchemaVariableCollector coll2  = new TacletSchemaVariableCollector();
	    taclet2.find().execPostOrder(coll2);
	    int formulaSV2 = countFormulaSV(coll2);
	
	    int cmpVar1 = -coll1.size()+taclet1.getRuleSets().size();
	    int cmpVar2 = -coll2.size()+taclet2.getRuleSets().size();
		    
	    if (cmpVar1 == cmpVar2) {
		cmpVar1 = cmpVar1-formulaSV1;
		cmpVar2 = cmpVar2-formulaSV2;
	    }
		    
	    if ( cmpVar1 < cmpVar2 ) {
		return -1;
	    } else if (cmpVar1 > cmpVar2) {
		return 1;
	    }
	
	    if (taclet1.ifSequent() == Sequent.EMPTY_SEQUENT && 
		taclet2.ifSequent() != Sequent.EMPTY_SEQUENT) {
		return 1;
	    } else if (taclet1.ifSequent() == Sequent.EMPTY_SEQUENT && 
		       taclet2.ifSequent() != Sequent.EMPTY_SEQUENT) {
		return -1;
	    }
		    
	    int goals1 = -taclet1.goalTemplates().size();
	    int goals2 = -taclet2.goalTemplates().size();
	
	    if (goals1 == goals2) {
		goals1 = -measureGoalComplexity(taclet1.goalTemplates());
		goals2 = -measureGoalComplexity(taclet2.goalTemplates());		
	    } 
	
	    if (goals1 < goals2) {
		return -1;
	    } else if (goals1 > goals2) {
		return 1;
	    }
	
	    return 0;
	}
	
    }
    
}
