// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.*;

import javax.swing.*;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.smt.RuleLauncher;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.smt.SMTRule;


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
     * @param findList IList<Taclet> with all applicable FindTaclets
     * @param rewriteList IList<Taclet> with all applicable RewriteTaclets
     * @param noFindList IList<Taclet> with all applicable noFindTaclets
     * @param builtInList IList<BuiltInRule> with all applicable BuiltInRules
     * @param pos the PosInSequent
     */ 
    TacletMenu(SequentView sequentView,
	       ImmutableList<TacletApp> findList, ImmutableList<TacletApp> rewriteList,
	       ImmutableList<TacletApp> noFindList, ImmutableList<BuiltInRule> builtInList,
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
     * @param list the IList<Taclet> from where the RewriteTaclet are
     * removed
     * @return list without RewriteTaclets
     */
    private ImmutableList<TacletApp> removeRewrites(ImmutableList<TacletApp> list) {
	ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
	Iterator<TacletApp> it = list.iterator();

	while(it.hasNext()) {
	    TacletApp tacletApp = it.next();
	    Taclet taclet=tacletApp.taclet();
	    result = (taclet instanceof RewriteTaclet ? result :
		      result.prepend(tacletApp));
	}
	return result;
    }


    /** creates the menu by adding all submenus and items */
    private void createTacletMenu(ImmutableList<TacletApp> find,
				  ImmutableList<TacletApp> noFind,
				  ImmutableList<BuiltInRule> builtInList,
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

    private void createBuiltInRuleMenu(ImmutableList<BuiltInRule> builtInList,
				       MenuControl            control) {

	if (!builtInList.isEmpty()) {
	    addSeparator();	
	    Iterator<BuiltInRule> it = builtInList.iterator();
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
        JMenuItem item;
        item = new DefaultBuiltInRuleMenuItem(builtInRule);                       
        item.addActionListener(control);
        add(item);
    }

    
    private void createFocussedAutoModeMenu (MenuControl control) {
        addSeparator();
        JMenuItem item = new FocussedRuleApplicationMenuItem ();
        item.addActionListener(control);
        add(item);        
    }
    

    private ImmutableList<TacletApp> sort(ImmutableList<TacletApp> finds) {
	ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
	
	List<TacletApp> list = new ArrayList<TacletApp>(finds.size());

	for (final TacletApp app : finds) {
	    list.add(app);
	}

	Collections.sort(list, comp);

	for (final TacletApp app : list) {
	    result = result.prepend(app);
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
     * @param taclet IList<Taclet> that contains the Taclets belonging to this section
     * @return true if section has been added (empty sections are not added)
     */ 
    private boolean addSection(String title, ImmutableList<TacletApp> taclet, 
			       MenuControl control) {
	if (taclet.size() > 0) {
	    //uncomment if you want submenus with subtitles
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
     * @param taclets IList<Taclet> with the Taclets the items represent
     * @param control the ActionListener
     * @return the new MenuItems
     */
    private TacletMenuItem[] createMenuItems(ImmutableList<TacletApp> taclets, 
					     MenuControl  control) {
	List<TacletMenuItem> items = new LinkedList<TacletMenuItem>();
	Iterator<TacletApp> it = taclets.iterator();
	
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
        
	return items.toArray(new TacletMenuItem[items.size()]);
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
            } else if (e.getSource() instanceof BuiltInRuleMenuItem) {
        	if (((BuiltInRuleMenuItem) e.getSource()).connectedTo() instanceof SMTRule) {
        	    SMTRule rule = (SMTRule) ((BuiltInRuleMenuItem) e.getSource()).connectedTo();
        	    RuleLauncher.INSTANCE.start(rule, Main.getInstance().mediator().getSelectedGoal(),
        		    Main.getInstance().mediator().getProof().getUserConstraint().getConstraint(),true);
      
        	} else {
                        mediator.selectedBuiltInRule
                    (((BuiltInRuleMenuItem) e.getSource()).connectedTo(), 
                     pos.getPosInOccurrence());
        	}
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
    
    
    static class TacletAppComparator implements Comparator<TacletApp> {

	private int countFormulaSV(TacletSchemaVariableCollector c) {
	    int formulaSV = 0;
	    Iterator<SchemaVariable> it = c.varIterator();
	    while (it.hasNext()) {
		SchemaVariable sv = it.next();
		if (sv instanceof FormulaSV) {
		    formulaSV++;
		}
	    }
	
	    return formulaSV;
	}
	
	/** this is a rough estimation about the goal complexity. The
	 * complexity depends on the depth of the term to be replaced.
	 * If no such term exists we add a constant (may be refined in
	 * future)
	 */
	private int measureGoalComplexity(ImmutableList<TacletGoalTemplate> l) {
	    int result = 0;
	    Iterator<TacletGoalTemplate> it = l.iterator();
	    while (it.hasNext()) {
		TacletGoalTemplate gt = it.next();
		if (gt instanceof RewriteTacletGoalTemplate) {
		    if (((RewriteTacletGoalTemplate)gt).replaceWith() != null) {
			result += ((RewriteTacletGoalTemplate)gt).replaceWith().depth();
		    }
		} 
		if (!gt.sequent().isEmpty()) {
		    result += 10;
		}
	    }
	    return result;
	}
	
	
	/**
	 * rough approximation of the program complexity
	 */
	public int programComplexity(JavaBlock b) {
	    if (b.isEmpty()) {
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
	
	public int compare(TacletApp o1, TacletApp o2) {
	    final Taclet taclet1 = o1.taclet();
	    final Taclet taclet2 = o2.taclet();
		
            int formulaSV1 = 0;
            int formulaSV2 = 0;

            int cmpVar1 = taclet1.getRuleSets().size();
            int cmpVar2 = taclet2.getRuleSets().size();

	    if (taclet1 instanceof FindTaclet && taclet2 instanceof FindTaclet) {
	        final Term find1 = ((FindTaclet) taclet1).find();
	        int findComplexity1 = find1.depth();
	        final Term find2 = ((FindTaclet) taclet2).find();
	        int findComplexity2 = find2.depth();
	        findComplexity1 += programComplexity(find1.javaBlock());
	        findComplexity2 += programComplexity(find2.javaBlock());

	        if ( findComplexity1 < findComplexity2 ) {
	            return -1;
	        } else if (findComplexity1 > findComplexity2) {
	            return 1;
	        }		    		    		    
	        // depth are equal. Number of schemavariables decides
	        TacletSchemaVariableCollector coll1 = new TacletSchemaVariableCollector();
	        find1.execPostOrder(coll1);
	        formulaSV1 = countFormulaSV(coll1);

	        TacletSchemaVariableCollector coll2  = new TacletSchemaVariableCollector();
	        find2.execPostOrder(coll2);
	        formulaSV2 = countFormulaSV(coll2);
	        cmpVar1 += -coll1.size();
	        cmpVar2 += -coll2.size();

	    } else if (taclet1 instanceof FindTaclet != taclet2 instanceof FindTaclet) {
	        if (taclet1 instanceof FindTaclet) {
	            return -1;
	        } else {
	            return 1;
	        }
	    }

	    if (cmpVar1 == cmpVar2) {
		cmpVar1 = cmpVar1-formulaSV1;
		cmpVar2 = cmpVar2-formulaSV2;
	    }
		    
	    if ( cmpVar1 < cmpVar2 ) {
		return -1;
	    } else if (cmpVar1 > cmpVar2) {
		return 1;
	    }
	
	    if (taclet1.ifSequent().isEmpty() && 
		!taclet2.ifSequent().isEmpty()) {
		return 1;
	    } else if (!taclet1.ifSequent().isEmpty() && 
		       taclet2.ifSequent().isEmpty()) {
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
