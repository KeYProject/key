// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export;

import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;

public class RuleExportModel {

    // keys: String, values: DisplayNameModelInfo
    private HashMap string2displayName = new HashMap ();
    // keys: RuleSet, values: RuleSetModelInfo
    private HashMap ruleSet2info = new HashMap ();
    // keys: String, values: CategoryModelInfo
    private HashMap category2info = new HashMap ();
    // keys: Choice, values: OptionModelInfo
    private HashMap choice2info = new HashMap ();

    private ImmutableList<TacletModelInfo>      taclets;
    private ImmutableList<RuleSetModelInfo>     ruleSets;
    private ImmutableList<DisplayNameModelInfo> displayNames;
    private ImmutableList<OptionModelInfo>      options;
    private ImmutableList<CategoryModelInfo>    categories;
	private final RuleFilter[] virtualRSFilterArray;
	private final RuleSetModelInfo[] virtualRSModelInfoArray;
	
	private static final String rsClosureDefinition = "Contains all taclets that create zero new goals.";
	private static final String rsSplitDefinition = "Contains all taclets that create more than one new goal.";
	private static final String rsUnassignedDefinition = "Contains all taclets that are not assigned an explicit rule set.";
    
    public RuleExportModel () {
        taclets = ImmutableSLList.<TacletModelInfo>nil();
        ruleSets = ImmutableSLList.<RuleSetModelInfo>nil();
        displayNames = ImmutableSLList.<DisplayNameModelInfo>nil();
        options = ImmutableSLList.<OptionModelInfo>nil();
		virtualRSFilterArray = new RuleFilter[] {
				TacletFilterCloseGoal.INSTANCE,
				TacletFilterSplitGoal.INSTANCE,
				new NotRuleFilter(AnyRuleSetTacletFilter.INSTANCE)
		};
		virtualRSModelInfoArray = new RuleSetModelInfo[] {
				new RuleSetModelInfo(new RuleSet(new Name("<closure>")), rsClosureDefinition, true),
				new RuleSetModelInfo(new RuleSet(new Name("<split>")), rsSplitDefinition, true),
				new RuleSetModelInfo(new RuleSet(new Name("<unassigned>")), rsUnassignedDefinition, true)
		};
		ruleSets = ruleSets.append ( virtualRSModelInfoArray );
    }
    
    private void addIntroducedTaclets ( TacletModelInfo tinfo, String filename ) {
        final Taclet t = tinfo.getTaclet ();
        Iterator<TacletGoalTemplate> it = t.goalTemplates ().iterator();
        while ( it.hasNext () ) {
            final TacletGoalTemplate gt = it.next ();
            
            addTaclets ( gt.rules(), filename, tinfo );
        }
    }
    
    public void addTaclet ( Taclet t, String filename ) {
        addTaclet ( t, filename, null );
    }
    
    private void addTaclet ( Taclet t, String filename, TacletModelInfo introducer ) {
        // add taclet
        final TacletModelInfo tinfo = new TacletModelInfo ( t, filename );
        taclets = taclets.prepend ( tinfo );
        tinfo.setIntroducingTaclet ( introducer );
        
        addIntroducedTaclets ( tinfo, filename );

        // add display name
        addDisplayName ( tinfo );
        
        // add rule sets
        addRuleSets ( tinfo );
        
        // add options
        addOptions ( tinfo );
    }
    
    private void addDisplayName ( TacletModelInfo tinfo ) {
        final Taclet t = tinfo.getTaclet();
        DisplayNameModelInfo dninfo = getTacletDisplayName ( t );
        if (dninfo == null) {
            String s = t.displayName ();
            dninfo = new DisplayNameModelInfo ( s );
            string2displayName.put ( s, dninfo );
            displayNames = displayNames.prepend ( dninfo );
        }
        dninfo.addTaclet(tinfo);
        tinfo.setDisplayName(dninfo);
    }

    private void addOptions ( TacletModelInfo tinfo ) {
        final Taclet t = tinfo.getTaclet ();
        final Iterator<Choice> it = t.getChoices().iterator();
        while ( it.hasNext() ) {
            final Choice c = it.next ();
            OptionModelInfo opt = addOption ( c );
            opt.addTaclet(tinfo);
            tinfo.addOption(opt);
        }
    }

    private OptionModelInfo addOption ( Choice c ) {
        OptionModelInfo opt = (OptionModelInfo) choice2info.get ( c );
        if ( opt == null ) {
            opt = new OptionModelInfo(c);
            choice2info.put ( c, opt );
            options = options.prepend(opt);
        }
        
        CategoryModelInfo cat = addCategory ( opt );
        opt.setCategory(cat);
        return opt;
    }

    private CategoryModelInfo addCategory ( OptionModelInfo opt ) {
        final Choice c = opt.getChoice();
        CategoryModelInfo cat = (CategoryModelInfo) category2info.get ( c.category() );
        if ( cat == null ) {
            cat = new CategoryModelInfo ( c.category() );
            category2info.put ( c.category(), cat );
        }
        cat.addOption ( opt );
        return cat;
    }

    private void addRuleSets ( TacletModelInfo tinfo ) {
    	final Taclet t = tinfo.getTaclet ();
    	// handle regular rule sets
        final Iterator<RuleSet> it = t.ruleSets();
        while ( it.hasNext() ) {
            final RuleSet rs = it.next ();
            RuleSetModelInfo rsinfo = (RuleSetModelInfo) ruleSet2info.get ( rs );
            if ( rsinfo == null ) {
                rsinfo = new RuleSetModelInfo(rs);
                ruleSet2info.put ( rs, rsinfo );
                ruleSets = ruleSets.prepend ( rsinfo );
            }
            rsinfo.addTaclet(tinfo);
            tinfo.addRuleSet(rsinfo);
        }
        // handle virtual rule sets
        for ( int n = 0; n < virtualRSFilterArray.length; n++ ) {
        	if ( virtualRSFilterArray[n].filter( t ) ) {
        		final RuleSetModelInfo rsinfo = virtualRSModelInfoArray[n];
        		rsinfo.addTaclet(tinfo);
        		tinfo.addRuleSet(rsinfo);
        	}
        }
    }

    private void addTaclets ( ImmutableList<Taclet> tacletList, String filename,
            TacletModelInfo introducer ) {
        final Iterator<Taclet> it = tacletList.iterator();
        while ( it.hasNext() ) {
            final Taclet t = it.next ();
            addTaclet ( t, filename, introducer );
        }
    }
    
    public void addTaclets ( ImmutableList<Taclet> tacletList, String filename ) {
        addTaclets ( tacletList, filename, null );
    }
    
    public void analyze () {
        taclets = sortTaclets ( taclets );

        ruleSets = sortRuleSets ( ruleSets );
        
        options = sortOptions ( options );

        displayNames = sortDisplayNames ( displayNames );
        
        analyzeDisplayNames ();
        
        analyzeCategories();
        
        analyzeOptions ();
        
        analyzeRuleSets ();
        
        analyzeTaclets ();
    }
    
    private void analyzeTaclets () {
        final Iterator<TacletModelInfo> it = taclets ();
        while ( it.hasNext () ) {
            final TacletModelInfo t = it.next ();
            t.setOptions(sortOptions(t.getOptions()));
            t.setRuleSets(sortRuleSets(t.getRuleSets()));
        }
    }

    private void analyzeOptions () {
        final Iterator<OptionModelInfo> it = options();
        while ( it.hasNext () ) {
            final OptionModelInfo opt = it.next ();
            opt.setTaclets(sortTaclets(opt.getTaclets()));
        }
    }

    private void analyzeDisplayNames () {
        final Iterator<DisplayNameModelInfo> it = displayNames();
        while ( it.hasNext () ) {
            final DisplayNameModelInfo dn = it.next ();
            dn.setTaclets(sortTaclets(dn.getTaclets()));
        }
    }

    /**
     *  
     */
    private void analyzeCategories() {
        Object[] objArray = category2info.values().toArray();
    	CategoryModelInfo[] catArray = new CategoryModelInfo[objArray.length];
        for (int n = 0; n < objArray.length; n++) {
            catArray[n] = (CategoryModelInfo) objArray[n];
        }
        Arrays.sort( catArray );
        categories = ImmutableSLList.<CategoryModelInfo>nil().prepend ( catArray );
        
        Iterator<CategoryModelInfo> it = categories.iterator();
        while ( it.hasNext () ) {
            final CategoryModelInfo cat = it.next ();
            cat.setOptions(sortOptions(cat.getOptions()));
        }
    }
    
    private void analyzeRuleSets () {
        ImmutableList<RuleSetModelInfo> outer = ruleSets;
        while ( !outer.isEmpty () ) {
            final RuleSetModelInfo ruleSet = outer.head ();
            outer = outer.tail ();
            
            ruleSet.setTaclets(sortTaclets(ruleSet.getTaclets()));
            
            ImmutableList<RuleSetModelInfo> inner = outer;
            while ( !inner.isEmpty () ) {
                final RuleSetModelInfo ruleSet2 = inner.head ();
                inner = inner.tail ();
                
                analyzeRuleSetRelationship ( ruleSet, ruleSet2 );
            }
            
        }
    }

    private void analyzeRuleSetRelationship ( RuleSetModelInfo rs, RuleSetModelInfo rs2 ) {
        ImmutableList<TacletModelInfo> list = rs.getTaclets();
        ImmutableList<TacletModelInfo> list2 = rs2.getTaclets();
        
        int a = countOccurences ( list, list2 );
        int b = countOccurences ( list2, list );
        
        if ( a == list.size () ) {
            // rule set 1 is a subset of rule set 2
            if ( b == list2.size() ) {
                // both rule sets are equal
                rs.addEqualSet ( rs2 );
                rs2.addEqualSet ( rs );
            } else {
                // rule set 1 is a true subset of rule set 2
                rs.addSuperSet ( rs2 );
                rs2.addSubSet ( rs );
            }
        } else if ( b == list2.size () ) {
            // rule set 2 is a true subset of rule set 1
            rs.addSubSet ( rs2 );
            rs2.addSuperSet ( rs );
        } else if ( a > 0 ) {
            // both rule sets intersect
            rs.addIntersectingSet ( rs2 );
            rs2.addIntersectingSet ( rs );
        }
    }

    /**
     * Counts the number of taclets from one list that are contained in a second
     * list.
     */
    private int countOccurences ( ImmutableList<TacletModelInfo> a, ImmutableList<TacletModelInfo> b ) {
        int result = 0;
        
        final Iterator<TacletModelInfo> it = a.iterator();
        while ( it.hasNext () ) {
            final TacletModelInfo t = it.next ();
            
            if ( b.contains ( t ) ) result++;
        }
        
        return result;
    }

    private ImmutableList<RuleSetModelInfo> sortRuleSets ( ImmutableList<RuleSetModelInfo> ruleSetList ) {
        RuleSetModelInfo[] ruleSetArray = ruleSetList.toArray (new RuleSetModelInfo[ruleSetList.size()]);
        Arrays.sort ( ruleSetArray, new NamedComparator () );
        return ImmutableSLList.<RuleSetModelInfo>nil().prepend ( ruleSetArray );
    }

    private ImmutableList<TacletModelInfo> sortTaclets ( ImmutableList<TacletModelInfo> tacletList ) {
        TacletModelInfo[] tacletArray = tacletList.toArray (new TacletModelInfo[tacletList.size()]);
        Arrays.sort ( tacletArray, new NamedComparator () );
        return ImmutableSLList.<TacletModelInfo>nil().prepend ( tacletArray );
    }
    
    private ImmutableList<OptionModelInfo> sortOptions ( ImmutableList<OptionModelInfo> optionList ) {
        OptionModelInfo[] optionArray = optionList.toArray(new OptionModelInfo[optionList.size()]);
        Arrays.sort ( optionArray, new NamedComparator () );
        return ImmutableSLList.<OptionModelInfo>nil().prepend(optionArray);
    }

    private ImmutableList<DisplayNameModelInfo> sortDisplayNames ( ImmutableList<DisplayNameModelInfo> displayNames ) {
        DisplayNameModelInfo[] displayNameArray = displayNames.toArray (new DisplayNameModelInfo[displayNames.size()]);
        Arrays.sort ( displayNameArray );
        return ImmutableSLList.<DisplayNameModelInfo>nil().prepend ( displayNameArray );
    }

    public ImmutableList<TacletModelInfo> getTaclets () {
        return taclets;
    }
    
    public Iterator<TacletModelInfo> taclets () {
        return getTaclets ().iterator ();
    }

    public ImmutableList<RuleSetModelInfo> getRuleSets () {
        return ruleSets;
    }
    
    public Iterator<RuleSetModelInfo> ruleSets () {
        return getRuleSets ().iterator ();
    }

    public ImmutableList<DisplayNameModelInfo> getDisplayNames () {
        return displayNames;
    }
    
    public Iterator<DisplayNameModelInfo> displayNames () {
        return displayNames.iterator ();
    }
    
    public ImmutableList<OptionModelInfo> getOptions () {
        return options;
    }
    
    public Iterator<OptionModelInfo> options () {
        return getOptions ().iterator ();
    }
    
    public ImmutableList<CategoryModelInfo> getCategories () {
        return categories;
    }
    
    public Iterator<CategoryModelInfo> categories () {
        return categories.iterator ();
    }
    
    private DisplayNameModelInfo getTacletDisplayName ( Taclet t ) {
        return (DisplayNameModelInfo)string2displayName.get ( t.displayName () );
    }
    
    private static class NamedComparator implements Comparator {

        public int compare ( Object a, Object b ) {
            return ((Named) a).name ().compareTo ( ((Named) b).name () );
        }
    }
}
