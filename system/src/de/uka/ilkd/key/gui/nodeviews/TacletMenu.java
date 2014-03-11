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


package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.*;

import javax.swing.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.join.JoinMenuItem;
import de.uka.ilkd.key.gui.macros.ProofMacroMenu;
import de.uka.ilkd.key.gui.smt.SMTMenuItem;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.join.JoinIsApplicable;
import de.uka.ilkd.key.proof.join.ProspectivePartner;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.util.GuiUtilities;


/**
 *  This class creates a menu with Taclets as entries. The invoker has
 * to be of type SequentView because of the method call selectedTaclet
 * that hands over the selected Taclet. The class is used to get all
 * Taclet that are applicable at a selected position in a sequent.
 */
class TacletMenu extends JMenu {

    private static final String MORE_RULES = "More rules";
	private static final String COPY_TO_CLIPBOARD = "Copy to clipboard";
	private static final String CREATE_ABBREVIATION = "Create abbreviation";
	private static final String ENABLE_ABBREVIATION = "Enable abbreviation";
	private static final String DISABLE_ABBREVIATION = "Disable abbreviation";
	private static final String CHANGE_ABBREVIATION = "Change abbreviation";
	private static final String APPLY_CONTRACT = "Apply Contract";
	private static final String CHOOSE_AND_APPLY_CONTRACT = "Choose and Apply Contract";
	private static final String ENTER_LOOP_SPECIFICATION = "Enter Loop Specification";
	private static final String APPLY_RULE = "Apply Rule";
	private static final String NO_RULES_APPLICABLE = "No rules applicable.";
	/**
     *
     */
    private static final long serialVersionUID = -4659105575090816693L;
    private PosInSequent pos;
    private CurrentGoalView sequentView;
    private KeYMediator mediator;
    private static final Set<Name> CLUTTER_RULESETS = new LinkedHashSet<Name>();

    static {
        CLUTTER_RULESETS.add(new Name("notHumanReadable"));
        CLUTTER_RULESETS.add(new Name("obsolete"));
        CLUTTER_RULESETS.add(new Name("pullOutQuantifierAll"));
        CLUTTER_RULESETS.add(new Name("pullOutQuantifierEx"));
    }
    private static final Set<Name> CLUTTER_RULES = new LinkedHashSet<Name>();

    static {
        CLUTTER_RULES.add(new Name("cut_direct_r"));
        CLUTTER_RULES.add(new Name("cut_direct_l"));
        CLUTTER_RULES.add(new Name("case_distinction_r"));
        CLUTTER_RULES.add(new Name("case_distinction_l"));
        CLUTTER_RULES.add(new Name("local_cut"));
        CLUTTER_RULES.add(new Name("commute_and_2"));
        CLUTTER_RULES.add(new Name("commute_or_2"));
        CLUTTER_RULES.add(new Name("boxToDiamond"));
        CLUTTER_RULES.add(new Name("pullOut"));
        CLUTTER_RULES.add(new Name("typeStatic"));
        CLUTTER_RULES.add(new Name("less_is_total"));
        CLUTTER_RULES.add(new Name("less_zero_is_total"));
    }

    private TacletAppComparator comp = new TacletAppComparator();

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
    TacletMenu(CurrentGoalView sequentView,
	       ImmutableList<TacletApp> findList, ImmutableList<TacletApp> rewriteList,
	       ImmutableList<TacletApp> noFindList, ImmutableList<BuiltInRule> builtInList,
	       PosInSequent pos) {
        super();
	this.sequentView = sequentView;
	this.mediator = sequentView.getMediator();
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


    /** creates the menu by adding all sub-menus and items */
    private void createTacletMenu(ImmutableList<TacletApp> find,
				  ImmutableList<TacletApp> noFind,
				  ImmutableList<BuiltInRule> builtInList,
				  MenuControl control) {
	addActionListener(control);

        ImmutableList<TacletApp> toAdd = sort(find);
        boolean rulesAvailable =  find.size() > 0;

        if (pos != null && pos.isSequent()) {
            rulesAvailable |= noFind.size() > 0;
            toAdd = toAdd.prepend(noFind);
        }

//         for (TacletApp a : find) {
//             System.out.print(a.taclet().name()+":");
// 	    System.out.println(comp.score(a));
//         }

	if (rulesAvailable) {
            createMenuItems(toAdd, control);
        } else {
	    createSection(NO_RULES_APPLICABLE);
	}

	createBuiltInRuleMenu(builtInList, control);

	if(pos!= null && pos.isSequent()){
	    createSMTMenu(control);
	}
	createFocussedAutoModeMenu ( control );
    addMacroMenu();
	ceateJoinMenu(control);

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

    private void addMacroMenu() {
        ProofMacroMenu menu = new ProofMacroMenu(mediator, pos.getPosInOccurrence());
        if(!menu.isEmpty()) {
//            addSeparator();
            add(menu);
        }
    }

        private void createSMTMenu(MenuControl control) {
                Collection<SolverTypeCollection> solverUnions = ProofIndependentSettings.DEFAULT_INSTANCE
                                .getSMTSettings().getSolverUnions();
                if (!solverUnions.isEmpty()) {
                        addSeparator();
                }
                for (SolverTypeCollection union : solverUnions) {
                        if (union.isUsable()) {
                                JMenuItem item = new SMTMenuItem(union);
                                item.addActionListener(control);
                                add(item);
                        }
                }

        }

        private void ceateJoinMenu(MenuControl control){

               List<ProspectivePartner> partner =
                       JoinIsApplicable.INSTANCE.isApplicable(mediator.getSelectedGoal(),pos.getPosInOccurrence());
               if(!partner.isEmpty()){
                   JMenuItem item = new JoinMenuItem(partner,mediator.getSelectedProof(),mediator);
                   if (JoinMenuItem.FEATURE.active()) add(item);
               }
        }

    /**
     * adds an item for built in rules (e.g. Run Simplify or Update Simplifier)
     */
    private void addBuiltInRuleItem(BuiltInRule builtInRule,
				    MenuControl control) {
        JMenuItem item;
        if (builtInRule == WhileInvariantRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            item = new MenuItemForTwoModeRules(builtInRule.displayName(),
                    APPLY_RULE, "Applies a known and complete loop specification immediately.",
                    ENTER_LOOP_SPECIFICATION, "Allows to modify an existing or to enter a new loop specification.", builtInRule);
            item.addActionListener(control);
            add(item);
        } else if (builtInRule == BlockContractRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            item = new MenuItemForTwoModeRules(builtInRule.displayName(),
                    APPLY_RULE, "Applies a known and complete block specification immediately.",
                    CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.", builtInRule);
            item.addActionListener(control);
            add(item);
        } else if (builtInRule == UseOperationContractRule.INSTANCE) {
            item = new MenuItemForTwoModeRules(builtInRule.displayName(),
                    APPLY_CONTRACT, "All available contracts of the method are combined and applied.",
                    CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.", builtInRule);
            item.addActionListener(control);
            add(item);
        } else {
            item = new DefaultBuiltInRuleMenuItem(builtInRule);
            item.addActionListener(control);
            add(item);
        }
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
	    sc = new JMenuItem(CHANGE_ABBREVIATION);
	    sc.addActionListener(control);
	    add(sc);
	    if(scm.isEnabled(t)){
		sc = new JMenuItem(DISABLE_ABBREVIATION);
	    }else{
		sc = new JMenuItem(ENABLE_ABBREVIATION);
	    }
	}else{
	    sc = new JMenuItem(CREATE_ABBREVIATION);
	}
	sc.addActionListener(control);
	add(sc);
    }


    private void createNameCreationInfoSection(MenuControl control) {
	JMenuItem item = new JMenuItem("View name creation info...");
	item.addActionListener(control);
	add(item);
    }


    /** inserts separator followed from the section's title
     * @param title a String that contains the title of the section
     */
    private void createSection(String title) {
	//addSeparator();
	add(new JLabel(title));
    }


    private void addClipboardItem(MenuControl control) {
	addSeparator();
	JMenuItem item = new JMenuItem(COPY_TO_CLIPBOARD);
	item.addActionListener(control);
	add(item);
    }


    /** adds a TacletMenuItem for each taclet in the list and sets
     * the given MenuControl as the ActionListener
     * @param taclets IList<Taclet> with the Taclets the items represent
     * @param control the ActionListener
     */
    private void createMenuItems(ImmutableList<TacletApp> taclets,
				 MenuControl  control) {

        final InsertHiddenTacletMenuItem insHiddenItem =
            new InsertHiddenTacletMenuItem(MainWindow.getInstance(),
                    mediator.getNotationInfo(), mediator.getServices());

        final InsertionTacletBrowserMenuItem insSystemInvItem =
            new InsertSystemInvariantTacletMenuItem(MainWindow.getInstance(),
                    mediator.getNotationInfo(), mediator.getServices());


        for (final TacletApp app : taclets) {
            final Taclet taclet = app.taclet();

            if (insHiddenItem.isResponsible(taclet)) {
                insHiddenItem.add(app);
            } else if (insSystemInvItem.isResponsible(taclet)) {
                insSystemInvItem.add(app);
            }
	}

        if (insHiddenItem.getAppSize() > 0) {
            add(insHiddenItem);
            insHiddenItem.addActionListener(control);
        }

        if (insSystemInvItem.getAppSize() > 0) {
            add(insSystemInvItem);
            insSystemInvItem.addActionListener(control);
        }

        JMenu more = new JMenu(MORE_RULES);

        for (final TacletApp app : taclets) {
            final Taclet taclet = app.taclet();
            if(!mediator.getFilterForInteractiveProving().filter(taclet)){
                continue;
            }

            if (! insHiddenItem.isResponsible(taclet) &&
                !insSystemInvItem.isResponsible(taclet)) {
                final DefaultTacletMenuItem item =
                    new DefaultTacletMenuItem(this, app,
                        mediator.getNotationInfo(), mediator.getServices());
                item.addActionListener(control);
                boolean rareRule = false;
                for (RuleSet rs : taclet.getRuleSets()) {
                    if (CLUTTER_RULESETS.contains(rs.name())) rareRule = true;
                }
                if (CLUTTER_RULES.contains(taclet.name())) rareRule = true;

                if (rareRule)
                    more.add(item);
                else add(item);
            }
	}

        if (more.getItemCount() > 0) add(more);
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
		((CurrentGoalView)(getPopupMenu().getInvoker()))
		    .selectedTaclet(((TacletMenuItem) e.getSource()).connectedTo(),
				    pos);
            }else if(e.getSource() instanceof SMTMenuItem){
        	final SMTMenuItem item = (SMTMenuItem) e.getSource();
        	final SolverTypeCollection solverUnion = item.getSolverUnion();
	    	final Goal goal = mediator.getSelectedGoal();
	    	assert goal != null;

        	Thread thread = new Thread(new Runnable() {
	        @Override
	        public void run() {

	            SMTSettings settings = new SMTSettings(goal.proof().getSettings().getSMTSettings(),
	                            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),goal.proof());
	            SolverLauncher launcher = new SolverLauncher(settings);
	            launcher.addListener(new SolverListener(settings));
	            Collection<SMTProblem> list = new LinkedList<SMTProblem>();
	            list.add(new SMTProblem(goal));
	           	launcher.launch(solverUnion.getTypes(),
			            list,
			            goal.proof().getServices());


        	}},"SMTRunner");
        	thread.start();
            }
            else if (e.getSource() instanceof BuiltInRuleMenuItem) {

                final BuiltInRuleMenuItem birmi = (BuiltInRuleMenuItem) e
                        .getSource();
                mediator.selectedBuiltInRule(
                        birmi.connectedTo(), pos.getPosInOccurrence(),
                        birmi.forcedApplication());

	    } else if (e.getSource() instanceof FocussedRuleApplicationMenuItem) {
	        mediator.getInteractiveProver ()
	            .startFocussedAutoMode ( pos.getPosInOccurrence (),
	                                     mediator.getSelectedGoal () );
	    } else {
		// TODO: change to switch statement once development switches to Java7
		if (((JMenuItem)e.getSource()).getText()
		    .startsWith(COPY_TO_CLIPBOARD)){
                    GuiUtilities.copyHighlightToClipboard(sequentView, pos);
		} else if(((JMenuItem)e.getSource()).getText().
			  startsWith(DISABLE_ABBREVIATION)){
		    PosInOccurrence occ = pos.getPosInOccurrence();
		    if (occ != null && occ.posInTerm() != null) {
			mediator.getNotationInfo().getAbbrevMap().setEnabled(occ.subTerm(),false);
			sequentView.printSequent();
		    }
		}else if(((JMenuItem)e.getSource()).getText().
			 startsWith(ENABLE_ABBREVIATION)){
		    PosInOccurrence occ = pos.getPosInOccurrence();
		    if (occ != null && occ.posInTerm() != null) {
			mediator.getNotationInfo().
			    getAbbrevMap().setEnabled(occ.subTerm(),true);
			sequentView.printSequent();
		    }
		}else if(((JMenuItem)e.getSource()).getText().
			 startsWith(CREATE_ABBREVIATION)){
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
			 startsWith(CHANGE_ABBREVIATION)){
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
        private static final String APPLY_RULES_AUTOMATICALLY_HERE = "Apply rules automatically here";
		/**
         *
         */
        private static final long serialVersionUID = -6486650015103963268L;

        public FocussedRuleApplicationMenuItem () {
            super(APPLY_RULES_AUTOMATICALLY_HERE);
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
            LinkedHashMap<String,Integer> map1 = score(o1);
            LinkedHashMap<String,Integer> map2 = score(o2);
            Iterator<Map.Entry<String,Integer> > it1 = map1.entrySet().iterator();
            Iterator<Map.Entry<String,Integer> > it2 = map2.entrySet().iterator();
            while (it1.hasNext() && it2.hasNext()) {
                String s1 = it1.next().getKey();
                String s2 = it2.next().getKey();
                if (!s1.equals(s2)) throw new IllegalStateException(
                    "A decision should have been made on a higher level ( "+
                    s1+"<->"+s2+")");
                int v1 = map1.get(s1);
                int v2 = map2.get(s2);
                // the order will be reversed when the list is sorted
                if (v1<v2) return 1;
                if (v1>v2) return -1;
            }
            return 0;
	}


        /* A score is a list of named values (comparable lexicographically).
           Smaller value means the taclet should be higher on the list
           offered to the user. Two scores need not contain the same
           named criteria, but the scoring scheme must force a decision
           before the first divergence point.
        */
	public LinkedHashMap<String,Integer> score(TacletApp o1) {
            LinkedHashMap<String,Integer> map = new LinkedHashMap<String,Integer>();

	    final Taclet taclet1 = o1.taclet();

            map.put("closing", taclet1.goalTemplates().size()==0 ? -1:1);

            boolean calc = false;
            for (RuleSet rs : taclet1.getRuleSets()) {
                String s = rs.name().toString();
                if (s.equals("simplify_literals") ||
                    s.equals("concrete") ||
                    s.equals("update_elim") ||
                    s.equals("replace_known_left") ||
                    s.equals("replace_known_right")) calc = true;
            }
            map.put("calc", calc ? -1 : 1);

            int formulaSV1 = 0;
            int cmpVar1 = 0;

	    if (taclet1 instanceof FindTaclet) {
                map.put("has_find", -1);

	        final Term find1 = ((FindTaclet) taclet1).find();
	        int findComplexity1 = find1.depth();
	        findComplexity1 += programComplexity(find1.javaBlock());
                map.put("find_complexity", -findComplexity1);

	        // depth are equal. Number of schemavariables decides
	        TacletSchemaVariableCollector coll1 = new TacletSchemaVariableCollector();
	        find1.execPostOrder(coll1);
	        formulaSV1 = countFormulaSV(coll1);
	        cmpVar1 += -coll1.size();
                map.put("num_sv", -cmpVar1);

	    } else {
                map.put("has_find", 1);
	    }

            cmpVar1 = cmpVar1-formulaSV1;
            map.put("sans_formula_sv", -cmpVar1);

            map.put("if_seq", taclet1.ifSequent().isEmpty() ? 1 : -1);

            map.put("num_goals", taclet1.goalTemplates().size());

            map.put("goal_compl", measureGoalComplexity(taclet1.goalTemplates()));

            return map;
	}



    }
}
