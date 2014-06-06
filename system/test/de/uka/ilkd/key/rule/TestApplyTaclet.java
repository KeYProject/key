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

package de.uka.ilkd.key.rule;

import java.util.Iterator;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.rulefilter.IHTacletFilter;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletSchemaVariableCollector;


/** 
 * class tests the apply methods in Taclet
 */
public class TestApplyTaclet extends TestCase{

    final static String[] strs={
	           "",
	           "(A -> B) -> (!(!(A -> B)))",
		   "",
		   "\\forall s z; p(z)",
		   "(A -> B) -> (!(!(A -> B)))",
		   "(A -> B) -> (!(!(A -> B)))",
		   "(A -> B) -> (!(!(A -> B)))",
		   "",		   
		   "","\\<{try{while (1==1) {if (1==2) {break;}} return 1==3; int i=17; } catch (Exception e) { return null;}}\\>A",
                   "A & B", 
                   "",
		   "",//"s{}::isEmpty(sset)",
		   "",//"s{}::size(sset)=0",
		   "A & (A & B)", "",
		   "f(const)=const", 
		   "const=f(f(const))",
		   "f(const)=const", 
		   "const=f(const)",
		   "f(const)=const", 
		   "A & {i:=0}(const=f(const))",
		   "f(const)=const", 
		   "A & {i:=0}(const=f(f(const)))",
		   "{i:=0}(f(const)=const)", 
		   "{i:=1}(const=f(const)) & \\<{i=2;}\\>(const=f(const)) " + "& {i:=0}(const=f(const))",
		   "{i:=0}(f(const)=const)", 
		   "{i:=1}(const=f(const)) & \\<{i=2;}\\>(const=f(const)) " + "& {i:=0}(const=const)",
                   "", 
                   "\\<{ {} {break;} }\\> true",
		   "", 
		   "\\<{ {{}} {{break;}} }\\> true",
		   "", 
		   "\\<{ try {} catch ( Exception e ) {} catch ( Throwable e ) {} }\\> true",
		   "", 
		   "\\<{ try {} catch ( Exception e ) {} try {} catch ( Throwable e ) {} }\\> true",
		   "", 
		   "\\<{ try {} catch ( Exception e ) {break;} catch ( Throwable e ) {continue;} }\\> true",
		   "", 
		   "\\<{ try {} catch ( Exception e ) {break;} try {} catch ( Throwable e ) {continue;} }\\> true",
		   "", 
		   "\\<{ try {} catch ( Exception e ) {} catch ( Throwable e ) {} finally {} }\\> true",
		   "", 
		   "\\<{ try {} catch ( Exception e ) {} finally {} try {} catch ( Throwable e ) {} }\\> true",
                   "", 
                   "\\<{try{while (1==1) {if (1==2) {break;}} return 1==3; int i=17; } catch (Exception e) { return null;}}\\>\\forall int i; i>0",
                   "", 
                   "\\<{try{ {} while (1==1) {if (1==2) {break;}} return 1==3; int i=17; } catch (Exception e) { return null;}}\\>\\forall int i; i>0"
    };
    Proof[] proof;
    

    public TestApplyTaclet(String name) {
	super(name);
       // Debug.ENABLE_DEBUG = true;

    }


    private static Semisequent parseTermForSemisequent(String t) {
	if ("".equals(t)) { 
	    return Semisequent.EMPTY_SEMISEQUENT;
	}
	SequentFormula cf0
	    = new SequentFormula(TacletForTests.parseTerm(t));
	return Semisequent.EMPTY_SEMISEQUENT.insert(0, cf0).semisequent();
    }

    public void setUp() {
	

	TacletForTests.setStandardFile(TacletForTests.testRules);
	TacletForTests.parse();
	assert TacletForTests.services().getNamespaces().programVariables().lookup(new Name("i")) != null;
	
	proof = new Proof[strs.length/2];
                        
        for (int i=0; i<proof.length; i++) {
	    Semisequent antec = parseTermForSemisequent(strs[2*i]);
	    Semisequent succ = parseTermForSemisequent(strs[2*i+1]);
	    Sequent s = Sequent.createSequent(antec, succ);	    
	    proof[i]=new Proof(TacletForTests.services());
	    proof[i].setRoot(new Node(proof[i], s));
	}
    }

    public void tearDown() {
        proof = null;
    }
    
    
    public void testSuccTacletWithoutIf() {
	Term fma = proof[0].root().sequent().succedent().getFirst().formula();
	NoPosTacletApp impright=TacletForTests.getRules().lookup("imp_right");
	TacletIndex tacletIndex = new TacletIndex ();
	tacletIndex.add ( impright );
	Goal goal = createGoal ( proof[0].root(), tacletIndex );
	PosInOccurrence applyPos= new 
			PosInOccurrence(goal.sequent().succedent().getFirst(),
					PosInTerm.getTopLevel(),
					false);
	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
		    getTacletAppAt(TacletFilter.TRUE, applyPos, null);	
	assertTrue("Too many or zero rule applications.",rApplist.size()==1);
	RuleApp rApp=rApplist.head();
	assertTrue("Rule App should be complete", rApp.complete());
	ImmutableList<Goal> goals=rApp.execute(goal, TacletForTests.services());
	assertTrue("Too many or zero goals for imp-right.",goals.size()==1);	
	Sequent seq=goals.head().sequent();
	assertEquals("Wrong antecedent after imp-right",
		     seq.antecedent().getFirst().formula(), fma.sub(0));  
       	assertEquals("Wrong succedent after imp-right",
		     seq.succedent().getFirst().formula(), fma.sub(1));  	
    }
    

    public void testAddingRule() {
	Term fma=proof[0].root().sequent().succedent().getFirst().formula();
	NoPosTacletApp imprightadd 
	    = TacletForTests.getRules().lookup("TestApplyTaclet_imp_right_add");
	TacletIndex tacletIndex = new TacletIndex ();
	tacletIndex.add ( imprightadd );
	Goal goal = createGoal ( proof[0].root(), tacletIndex );
	PosInOccurrence applyPos= new 
	    PosInOccurrence(goal.sequent().succedent().getFirst(), 
			    PosInTerm.getTopLevel(),
			    false);
	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
	    getTacletAppAt(TacletFilter.TRUE, applyPos,
			   null);	
	assertTrue("Too many or zero rule applications.",rApplist.size()==1);
	RuleApp rApp=rApplist.head();
	assertTrue("Rule App should be complete", rApp.complete());
	ImmutableList<Goal> goals=rApp.execute(goal, TacletForTests.services());
	assertTrue("Too many or zero goals for imp_right_add.",goals.size()==1);
	Sequent seq=goals.head().sequent();
	assertEquals("Wrong antecedent after imp_right_add",
		     seq.antecedent().getFirst().formula(),
		     fma.sub(0));  
       	assertEquals("Wrong succedent after imp_right_add",
		     seq.succedent().getFirst().formula(),
		     fma.sub(1));  
	ImmutableList<NoPosTacletApp> nfapp=goals.head().indexOfTaclets().getNoFindTaclet
	    (new IHTacletFilter ( true, ImmutableSLList.<RuleSet>nil() ), 
	     null);
	Term aimpb=TacletForTests.parseTerm("A -> B");
	assertTrue("Cut Rule should be inserted to TacletIndex.", nfapp.size()==1);
	assertTrue("Inserted cut rule's b should be instantiated to A -> B.",
		   nfapp.head().instantiations().getInstantiation
		   ((SchemaVariable)TacletForTests.getVariables().lookup(new Name("b")))
		   .equals(aimpb));
	assertTrue("Rule App should be complete", rApp.complete());
	goals=nfapp.head().execute(goals.head(), TacletForTests.services());
	Sequent seq1=goals.head().sequent();
	Sequent seq2=goals.tail().head().sequent();
	assertTrue("Preinstantiated cut-rule should be executed", goals.size()==2);
	assertTrue("A->B should be in the succedent of one of the new goals now, "
		   +"it's in the antecedent, anyway.",
		   seq1.succedent().getFirst().formula().equals(aimpb) || 
		   seq2.succedent().getFirst().formula().equals(aimpb) ||
		   (seq1.succedent().get(1)!=null 
		    && seq1.succedent().get(1).formula().equals(aimpb)) ||
		   (seq2.succedent().get(1)!=null 
		    && seq2.succedent().get(1).formula().equals(aimpb)));
    }

    
    public void testSuccTacletAllRight() {
	NoPosTacletApp allright = TacletForTests.getRules().lookup("all_right");
	TacletIndex tacletIndex = new TacletIndex ();
	tacletIndex.add ( allright );
	Goal goal = createGoal ( proof[1].root(), tacletIndex );
	PosInOccurrence applyPos
	    = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
				  PosInTerm.getTopLevel(),
				  false);	
	ImmutableList<TacletApp> rApplist = goal.ruleAppIndex().
		    getTacletAppAt(TacletFilter.TRUE, applyPos, null);
	assertTrue("Too many or zero rule applications.", rApplist.size()==1);
	RuleApp rApp=rApplist.head();
	rApp = ((TacletApp)rApp).tryToInstantiate ( TacletForTests.services() );
	assertTrue("Rule App should be complete", rApp.complete());
	ImmutableList<Goal> goals = rApp.execute(goal, TacletForTests.services());
	assertTrue("Too many or zero goals for all-right.",goals.size()==1);	
	Sequent seq=goals.head().sequent();
	assertEquals("Wrong antecedent after all-right",seq.antecedent(),
		     Semisequent.EMPTY_SEMISEQUENT);  
       	assertEquals("Wrong succedent after all-right (op mismatch)",
		     seq.succedent().getFirst().formula().op(),
		     TacletForTests.getFunctions().lookup(new Name("p")));  	
    }
    
    public void testTacletWithIf() {
        NoPosTacletApp close = TacletForTests.getRules().lookup("close_goal");
	TacletIndex tacletIndex = new TacletIndex ();
	tacletIndex.add ( close );
	Goal goal = createGoal ( proof[2].root(), tacletIndex );
	PosInOccurrence applyPos=new PosInOccurrence
	    (goal.sequent().succedent().getFirst(), 
	     PosInTerm.getTopLevel(),
	     false);
 	ImmutableList<TacletApp> rApplist
	    = goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE,
                applyPos, null);
 	assertTrue("Too many or zero rule applications.\napp list:"+rApplist,rApplist.size()==1);

 	TacletApp rApp=rApplist.head();
	ImmutableList<TacletApp> appList = 
	    rApp.findIfFormulaInstantiations ( goal.sequent (), 
	                                       TacletForTests.services() );
	assertTrue("Match Failed.", !appList.isEmpty());
	assertTrue("Too many matches.", appList.size()==1);
	assertTrue("Wrong match found.", appList.head().instantiations()==rApp.instantiations());
	assertTrue("Rule App should be complete", appList.head().complete());
 	ImmutableList<Goal> goals=appList.head ().execute(goal, TacletForTests.services());
	assertTrue("Wrong number of goals for close.", goals.size()==1);		
	proof[2].closeGoal ( goals.head ());
	assertTrue("Proof should be closed.", proof[2].closed ());		
	/*
 	IList<SVInstantiations> svilist=rApp.taclet().matchIf(goal.sequent(),
					   rApp.instantiations(), null);
	assertTrue("Match Failed.", !svilist.isEmpty());
	assertTrue("Too many matches.", svilist.size()==1);
	assertTrue("Wrong match found.", svilist.head()==rApp.instantiations());
	assertTrue("Rule App should be complete", rApp.complete());
 	IList<Goal> goals=rApp.execute(goal, TacletForTests.services());
	assertTrue("Too many goals for close.", goals.size()==0);		
	*/
    }

    
    public void testAntecTacletWithoutIf() {
	Term fma=proof[3].root().sequent().antecedent().getFirst().formula();
	NoPosTacletApp impleft = TacletForTests.getRules().lookup("imp_left");
 	TacletIndex tacletIndex = new TacletIndex ();
 	tacletIndex.add ( impleft );
 	Goal goal = createGoal ( proof[3].root(), tacletIndex );
	PosInOccurrence applyPos= new PosInOccurrence
	    (goal.sequent().antecedent().getFirst(), 
	     PosInTerm.getTopLevel(),
	     true);
 	ImmutableList<TacletApp> rApplist
	    = goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE,
	            applyPos, null);
 	assertTrue("Too many or zero rule applications.",rApplist.size()==1);
 	RuleApp rApp=rApplist.head();
	assertTrue("Rule App should be complete", rApp.complete());
 	ImmutableList<Goal> goals=rApp.execute(goal, TacletForTests.services());
 	assertTrue("Too many or zero goals for imp-left.",goals.size()==2);	
	Sequent seq=goals.head().sequent();
	if (!seq.succedent().isEmpty()) {
	    assertEquals("Wrong succedent after imp-left",
			 seq.succedent().getFirst().formula(),
			 fma.sub(0));  
	    goals=goals.tail();
	    seq=goals.head().node().sequent();
	    assertEquals("Wrong antecedent after imp-left",
			 seq.antecedent().getFirst().formula(),
			 fma.sub(1));  
	} else {
	    assertEquals("Wrong antecedent after imp-left",
			 seq.antecedent().getFirst().formula(),
			 fma.sub(1));  
	    goals=goals.tail();
	    seq=goals.head().node().sequent();

	    assertEquals("Wrong succedent after imp-left",
			 seq.succedent().getFirst().formula(),
			 fma.sub(0));  
	}
    }


    
    public void testRewriteTacletWithoutIf() {
	NoPosTacletApp contradiction = TacletForTests.getRules().lookup
	    ("TestApplyTaclet_contradiction");
	TacletIndex tacletIndex = new TacletIndex();
 	tacletIndex.add ( contradiction );
	Goal goal = createGoal ( proof[0].root(), tacletIndex );
	PosInOccurrence pos
	    = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
				  PosInTerm.getTopLevel().down(1).down(0).down(0),
				  false);
 	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
	    getTacletAppAt(TacletFilter.TRUE, pos, null);	

	assertTrue("Too many or zero rule applications.",rApplist.size()==1);
	RuleApp rApp=rApplist.head();
	assertTrue("Rule App should be complete", rApp.complete());
	ImmutableList<Goal> goals=rApp.execute(goal, TacletForTests.services());
	assertTrue("Too many or zero goals for contradiction.",goals.size()==1);	
	Sequent seq=goals.head().sequent();
	Term term=seq.succedent().getFirst().formula().sub(1).sub(0).sub(0);
	assertTrue(term.equals(TacletForTests.parseTerm("!B -> !A")));
    }


    public void testNoFindTacletWithoutIf() {
	NoPosTacletApp cut = TacletForTests.getRules().lookup("TestApplyTaclet_cut");
	TacletIndex tacletIndex = new TacletIndex ();
	Term t_c=TacletForTests.parseTerm("D");
 	tacletIndex.add ( cut );
	Goal goal = createGoal ( proof[0].root(), tacletIndex );
	PosInOccurrence pos
	    = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
				  PosInTerm.getTopLevel(),
				  false);
 	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
 		    getTacletAppAt(TacletFilter.TRUE, pos, null);	
	assertTrue("Too many or zero rule applications.",rApplist.size()==1);
	TacletApp rApp=rApplist.head().addInstantiation
	    ((SchemaVariable)TacletForTests.getVariables().lookup(new Name("b")), 
             t_c, 
             false,
             proof[0].getServices());
	assertTrue("Rule App should be complete", rApp.complete());
 	ImmutableList<Goal> goals=rApp.execute(goal, TacletForTests.services());
 	assertTrue("Too many or too few goals.",goals.size()==2);	
 	Sequent seq1=goals.head().sequent();
 	goals=goals.tail();
 	Sequent seq2=goals.head().sequent();
	if (!seq1.antecedent().isEmpty() 
	    && seq1.antecedent().getFirst().formula().equals(t_c)) {
	    assertTrue("D is in antecedent of 1st goal but not in succedent of 2nd",
		       seq2.succedent().getFirst().formula().equals(t_c)
		       || seq2.succedent().get(1).formula().equals(t_c));
	} else {
	    assertTrue("D is not in antecedent and not in succedent "
		       +"of first new goal",
		       seq1.succedent().getFirst().formula().equals(t_c)
		       || seq1.succedent().get(1).formula().equals(t_c));	    
	    assertTrue("D is in succedent of first new goal, but not in antecedent "
		       +"of second new goal",
		       seq2.antecedent().getFirst().formula().equals(t_c));
	}
    }




    /*    
    public String automaticProof(Sequent initSeq, TacletIndex index){
	String out="";
	Proof proof=new Proof();
	proof.setRoot(new Node(proof, initSeq));
	IList<Goal> goals=ImmSLList.<Goal>nil();
	Goal goal=new Goal(proof.root(),new RuleAppIndex(index));
	goals=goals.prepend(goal);
	while (goals.size()!=0) {
	    SequentFormula cfma=null;
	    SequentFormula userCfma=null;   // in the real system the 
		                              //user would select this
	    IList<TacletApp> rapplist=ImmSLList.<TacletApp>nil();
	    out="\n"+out+("Goals: "+goals+"\n");
	    goal=goals.head();
	    Iterator<SequentFormula>
		it=goal.node().sequent().antecedent().iterator();
	    while (it.hasNext()) {
		userCfma=it.next();
		rapplist=rapplist.prepend(goal.ruleAppIndex().
		    getTacletAppAtAndBelow(TacletFilter.TRUE, new 
			PosInOccurrence(userCfma, PosInTerm.TOP_LEVEL,
					goal.node().sequent())));
	    }
       	    if (rapplist.isEmpty()) {
		it=goal.node().sequent().succedent().iterator();
		while (it.hasNext()) {		
		    userCfma=it.next();	
		    rapplist=rapplist.prepend(goal.ruleAppIndex()
			.getTacletAppAtAndBelow(TacletFilter.TRUE, new 
			    PosInOccurrence(userCfma, PosInTerm.TOP_LEVEL,
					    goal.node().sequent()))) ;
		}
	    }
	    out="\n"+out+("GOAL INDEX:"+goal.indexOfTaclets());
	    out="\n"+out+("Rule apps: "+rapplist);
	    out="\n"+out+("Choose for if-test: "+rapplist.head()+"\n");
	    goals=goals.tail();
	    boolean executed=false;
	    while (!executed && !rapplist.isEmpty()) {
		IList<ImmMap<SchemaVariable,Term>>
		    mrlist=((Taclet)(rapplist.head().rule())).matchIf(goal.node().sequent(), 
								    rapplist.head().instantiations());
		out="\n"+out+("List of if-seq matches:"+mrlist);
		if (!mrlist.isEmpty()) {		
		    out+="Execute: "+rapplist.head()+"\n";
		    goals=goals.prepend(rapplist.head().execute(goal));	
		    executed=true;
		}
		rapplist=rapplist.tail();
	    }
	    out="\n"+out+("Tree: "+proof.root()+"\n *** \n");
	    if (!executed) {
		return out+"\nPROOF FAILED.";
	    }
	}
	if (goals.size()==0) out=out+"\nPROOF.";
	return out;
    }


    public void testNatAutomatically() {
	TacletAppIndex index=new TacletAppIndex(new TacletIndex());
      	index.addTaclet(TacletForTests.getRules().lookup("close_goal"));
	index.addTaclet(TacletForTests.getRules().lookup("imp_left"));
	index.addTaclet(TacletForTests.getRules().lookup("imp_right"));
	index.addTaclet(TacletForTests.getRules().lookup("not_left"));
	index.addTaclet(TacletForTests.getRules().lookup("not_right"));
	index.addTaclet(TacletForTests.getRules().lookup
		      ("TestApplyTaclet_predsuccelim"));
	index.addTaclet(pluszeroelim);
	index.addTaclet(zeropluselim);
	index.addTaclet(succelim);
	index.addTaclet(switchsecondsucc);
	index.addTaclet(switchfirstsucc);
	index.addTaclet(closewitheq);
	String s=(automaticProof(seq_testNat, index));
	assertTrue("Automatic proof with nats failed",
	           s.substring(s.length()-6).equals("PROOF."));
    }

*/

    public void testIncompleteNoFindTacletApp() {
	NoPosTacletApp cut = TacletForTests.getRules().lookup("TestApplyTaclet_cut");
	assertTrue("TacletApp should not be complete, as b is not instantiated",
		   !cut.complete());
	SchemaVariable b=(SchemaVariable)
	    TacletForTests.getVariables().lookup(new Name("b"));
	assertTrue("b should be in the set of not instantiated SVs",
		   cut.uninstantiatedVars().contains(b));
    }

    public void testIncompleteSuccTacletApp() {
	TacletApp orright = TacletForTests.getRules().lookup("or_right");
	assertTrue("TacletApp should not be complete, as SVs are not instantiated",
		   !orright.complete());

	Services services = TacletForTests.services();
	SchemaVariable b=(SchemaVariable)
	    TacletForTests.getVariables().lookup(new Name("b"));
	SchemaVariable c=(SchemaVariable)
	    TacletForTests.getVariables().lookup(new Name("c"));
	assertTrue("b and c should be in the set of not instantiated SVs",
		   orright.uninstantiatedVars()
		   .equals(DefaultImmutableSet.<SchemaVariable>nil().add(b).add(c)));
	orright=orright.addInstantiation(b,TacletForTests.parseTerm("A"), false, services);
	assertTrue("TacletApp should not be complete, as B is not instantiated",
		   !orright.complete());
	orright=orright.addInstantiation(c,TacletForTests.parseTerm("B"), false, services);
	assertTrue("TacletApp should not be complete, as Position unknown",
		   !orright.complete());
	Sequent seq=proof[0].root().sequent();
	orright=orright.setPosInOccurrence
	    (new PosInOccurrence(seq.succedent().get(0),
				 PosInTerm.getTopLevel(),
				 false),
				 services);
	assertTrue("TacletApp should now be complete with Position set and SVs "
		   +"instantiated",
		   orright.complete());
    }
    
    

    
    public void testPrgTacletApp() {
	NoPosTacletApp wh0 = TacletForTests.getRules().lookup("TestApplyTaclet_while0");
	SchemaVariable e2=(SchemaVariable)
	    TacletForTests.getVariables().lookup(new Name("#e2"));
	SchemaVariable p1=(SchemaVariable)
	    TacletForTests.getVariables().lookup(new Name("#p1"));
	//	wh0=wh0.addInstantiation(e2,TacletForTests.parseExpr("boolean", "false"));
	//	wh0=wh0.addInstantiation(p1,TacletForTests.parsePrg("{if (false){}}"));
	Sequent seq=proof[4].root().sequent();
	PosInOccurrence pio=new PosInOccurrence(seq.succedent().get(0),
						       PosInTerm.getTopLevel(),
						false);
	TacletIndex tacletIndex = new TacletIndex();
	tacletIndex.add ( wh0 );
	Goal goal = createGoal ( proof[4].root(), tacletIndex );
	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
	    getTacletAppAt(TacletFilter.TRUE, pio, null);

        final TacletApp app = rApplist.head();
        assertTrue("#e2 not instantiated", app.instantiations().isInstantiated(e2));
        assertTrue("#p1 not instantiated", app.instantiations().isInstantiated(p1));

        ImmutableList<Goal> goals = app.execute(goal, TacletForTests.services);
        
        assertTrue("Unexpected number of goals", goals.size() == 1);
    }

    
    public void testBugBrokenApply() {
	// several times the following bug got broken
	// The application of 
	//    'find (b==>) replacewith(b==>); add (==>b);'
	// resulted in 
	// ==>  ,   b==>b instead of
	// b==>  ,   b==>b 
	NoPosTacletApp cdr = 
	    TacletForTests.getRules().lookup("TestApplyTaclet_cut_direct_r");

	Sequent seq = proof[1].root().sequent();
	PosInOccurrence pio = new PosInOccurrence(seq.succedent().get(0),
						  PosInTerm.getTopLevel(),
						  false);
	TacletIndex tacletIndex = new TacletIndex();
	tacletIndex.add ( cdr );
	Goal goal = createGoal ( proof[1].root(), tacletIndex );
	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
	    getTacletAppAt(TacletFilter.TRUE, pio, null);
	ImmutableList<Goal> goals=rApplist.head().execute(goal, TacletForTests.services);

	assertTrue("Expected two goals", goals.size()==2);
	assertTrue("First goal should be 'b==>b', but is "+
		   goals.head().sequent(), 
		   goals.head().sequent().antecedent().size()  == 1 &&
		   goals.head().sequent().antecedent().iterator().
		   next().formula().op()==Quantifier.ALL &&
		   goals.head().sequent().succedent().size()  == 1 &&
		   goals.head().sequent().succedent().iterator().
		   next().formula().op()==Quantifier.ALL);
	goals = goals.tail();
	assertTrue("Second goal should be '==>b', but is "+
		   goals.head().sequent(), 
		   goals.head().sequent().antecedent().size() == 0 &&
		   goals.head().sequent().succedent().size()  == 1 &&
		   goals.head().sequent().succedent().iterator().
		   next().formula().op()==Quantifier.ALL);
	
    }

    public void testBugID176() {
	// the last time the bug above had been fixed, the hidden
	// taclets got broken (did not hide anymore)
	// also known as bug #176
	NoPosTacletApp hide_r = 
	    TacletForTests.getRules().lookup("TestApplyTaclet_hide_r");

	Sequent seq = proof[1].root().sequent();
	PosInOccurrence pio = new PosInOccurrence(seq.succedent().get(0),
						  PosInTerm.getTopLevel(),
						  false);
	TacletIndex tacletIndex = new TacletIndex();
	tacletIndex.add ( hide_r );
	Goal goal = createGoal ( proof[1].root(), tacletIndex );

	ImmutableList<TacletApp> rApplist = goal.ruleAppIndex().
	    getTacletAppAt(TacletFilter.TRUE, 
			   pio, null);
	ImmutableList<Goal> goals = rApplist.head().
	    execute(goal, TacletForTests.services());

	assertTrue("Expected one goal", goals.size()==1);
	assertTrue("Expected '==>', but is "+
		   goals.head().sequent(), 
		   goals.head().sequent().isEmpty());

    }

    public void testBugID177() {
	// bug #177
	NoPosTacletApp al = 
	    TacletForTests.getRules().lookup("and_left");

	Sequent seq = proof[5].root().sequent();
	PosInOccurrence pio = new PosInOccurrence(seq.antecedent().get(0),
				  PosInTerm.getTopLevel(),
				  true);
	TacletIndex tacletIndex = new TacletIndex();
	tacletIndex.add ( al );
	Goal goal = createGoal ( proof[5].root(), tacletIndex );

	ImmutableList<TacletApp> rApplist = goal.ruleAppIndex().
	    getTacletAppAt(TacletFilter.TRUE, 
			   pio, null);
	ImmutableList<Goal> goals = rApplist.head().
	    execute(goal, TacletForTests.services());


	assertTrue("Expected one goal", goals.size()==1);
	Iterator<SequentFormula> it = goals.head().sequent().
	    antecedent().iterator();
	assertTrue("Expected 'A, B ==>', but is "+
		   goals.head().sequent(), 
		   goals.head().sequent().antecedent().size() == 2 &&
		   it.next().formula().equals(TacletForTests.parseTerm("A")) &&
		   it.next().formula().equals(TacletForTests.parseTerm("B")));
    }

    public void testBugID188() {	
	//bug #188
	
	NoPosTacletApp al = TacletForTests.getRules().lookup("and_left");
	Sequent seq = proof[7].root().sequent();
	PosInOccurrence pio = new PosInOccurrence ( seq.antecedent().get(0),
				    PosInTerm.getTopLevel(),
				    true);

	TacletIndex tacletIndex = new TacletIndex ();
	tacletIndex.add ( al );

	Goal goal = createGoal ( proof[7].root(), tacletIndex );

	ImmutableList<TacletApp> rApplist = goal.ruleAppIndex().
	    getTacletAppAt(TacletFilter.TRUE, 
			   pio, null);
	ImmutableList<Goal> goals = rApplist.head().
	    execute(goal, TacletForTests.services());
	

       	seq = goals.head ().sequent ();
	pio = new PosInOccurrence ( seq.antecedent().get(1),
				    PosInTerm.getTopLevel(),
				    true);
	tacletIndex = new TacletIndex ();
	tacletIndex.add ( al );

	goal = createGoal ( goals.head().node(), tacletIndex );

	rApplist = goal.ruleAppIndex().
	    getTacletAppAt(TacletFilter.TRUE, 
			   pio, null);

	goals = rApplist.head().
	    execute(goal, TacletForTests.services());

	assertTrue("Expected one goal", goals.size()==1);

	Iterator<SequentFormula> it = 
	    goals.head().sequent().antecedent().iterator();

	assertTrue("Expected 'A, B ==>', but is "+
		   goals.head().sequent(), 
		   goals.head().sequent().antecedent().size() == 2 &&
		   goals.head().sequent().succedent().size() == 0 &&
		   it.next().formula().equals(TacletForTests.parseTerm("A")) &&
		   it.next().formula().equals(TacletForTests.parseTerm("B")));
    }


    public void testModalityLevel0 () {
	Services services = TacletForTests.services();
        NoPosTacletApp apply_eq_nonrigid = TacletForTests.getRules().lookup
	    ("apply_eq_nonrigid");
	TacletIndex tacletIndex = new TacletIndex ();
 	tacletIndex.add ( apply_eq_nonrigid );
	Goal goal = createGoal ( proof[8].root(), tacletIndex );
	PosInOccurrence pos
	    = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
				  PosInTerm.getTopLevel(),
				  false);
 	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
	    getTacletAppAtAndBelow(TacletFilter.TRUE, pos, services);	

	assertTrue("Expected four rule applications.",rApplist.size()==4);

	ImmutableList<TacletApp> appList = ImmutableSLList.<TacletApp>nil();
        for (TacletApp aRApplist : rApplist)
            appList = appList.prepend
                    (aRApplist.findIfFormulaInstantiations
                            (goal.sequent(), services));

	assertTrue("Expected one match.", appList.size()==1);
	assertTrue("Rule App should be complete", appList.head().complete());

 	ImmutableList<Goal> goals=appList.head ().execute(goal, TacletForTests.services());
	assertTrue("Too many or zero goals.",goals.size()==1);	
	Sequent seq=goals.head().sequent();
	Sequent correctSeq=proof[9].root().sequent();
	assertEquals("Wrong result", seq, correctSeq);
    }


    public void testModalityLevel1 () {
        Services services = TacletForTests.services();
	NoPosTacletApp apply_eq_nonrigid = TacletForTests.getRules().lookup    
	    ("apply_eq_nonrigid");
	TacletIndex tacletIndex = new TacletIndex ();
 	tacletIndex.add ( apply_eq_nonrigid );
	Goal goal = createGoal ( proof[10].root(), tacletIndex );
	PosInOccurrence pos
	    = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
				  PosInTerm.getTopLevel(),
				  false);
 	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
	    getTacletAppAtAndBelow(TacletFilter.TRUE, pos, 
                services);	

	assertTrue("Expected three rule applications.",rApplist.size()==3);

	ImmutableList<TacletApp> appList = ImmutableSLList.<TacletApp>nil();	
	Iterator<TacletApp> appIt = rApplist.iterator ();
	while ( appIt.hasNext () )
	    appList = appList.prepend
		( appIt.next ().findIfFormulaInstantiations ( goal.sequent (), 
		        services ) );

	assertTrue("Did not expect a match.", appList.size()==0);

	Term ifterm = TacletForTests.parseTerm("{i:=0}(f(const)=f(f(const)))");
	SequentFormula ifformula =
	    new SequentFormula ( ifterm );
	ImmutableList<IfFormulaInstantiation> ifInsts =
	    ImmutableSLList.<IfFormulaInstantiation>nil().prepend
	    ( new IfFormulaInstDirect ( ifformula ) );
	appIt = rApplist.iterator ();
	while ( appIt.hasNext () ) {
	    TacletApp a =
		appIt.next ().setIfFormulaInstantiations ( ifInsts,
							   TacletForTests.services() );
	    if ( a != null )
		appList = appList.prepend ( a );
	}

	assertTrue("Expected one match.", appList.size()==1);
	assertTrue("Rule App should be complete", appList.head().complete());

 	ImmutableList<Goal> goals=appList.head ().execute(goal, TacletForTests.services());
	assertTrue("Expected two goals.",goals.size()==2);

	{ // Goal one
	    Sequent correctSeq =
		proof[11].root ().sequent ()
		.addFormula ( ifformula, true, true ).sequent ();
	    assertEquals("Wrong result",
			 goals.head().sequent(),
			 correctSeq);
	}

	{ // Goal two
	    Sequent correctSeq =
		proof[10].root ().sequent ()
		.addFormula ( ifformula, false, true ).sequent ();
	    assertEquals("Wrong result",
			 goals.tail().head().sequent(),
			 correctSeq);
	}
    }


    public void testModalityLevel2 () {
        Services services = TacletForTests.services();
        NoPosTacletApp make_insert_eq_nonrigid = TacletForTests.getRules().lookup
	    ("make_insert_eq_nonrigid");
	TacletIndex tacletIndex = new TacletIndex ();
 	tacletIndex.add ( make_insert_eq_nonrigid );
	Goal goal = createGoal ( proof[12].root(), tacletIndex );
	PosInOccurrence pos
	    = new PosInOccurrence(goal.sequent().antecedent().getFirst(), 
				  PosInTerm.getTopLevel(),
				 true);
 	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
	    getTacletAppAtAndBelow(TacletFilter.TRUE, pos, services);	

	assertTrue("Expected one rule application.",rApplist.size()==1);
	assertTrue("Rule App should be complete", rApplist.head().complete());

 	ImmutableList<Goal> goals=rApplist.head ().execute(goal, TacletForTests.services());
	assertTrue("Expected one goal.",goals.size()==1);

	goal = goals.head ();

	pos = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
				  PosInTerm.getTopLevel(),
				  false);
 	rApplist=goal.ruleAppIndex().
	    getTacletAppAtAndBelow(TacletFilter.TRUE, pos, 
                services);	

	assertTrue("Expected one rule application.",rApplist.size()==1);
	assertTrue("Rule App should be complete", rApplist.head().complete());
	
 	goals=rApplist.head ().execute(goal, TacletForTests.services());
	assertTrue("Expected one goal.",goals.size()==1);

	Sequent seq=goals.head().sequent();
	Sequent correctSeq=proof[13].root().sequent();
	assertEquals("Wrong result", seq, correctSeq);
    }


    public void testBugEmptyBlock () {
	NoPosTacletApp testApplyTaclet_wrap_blocks_two_empty_lists =
	    TacletForTests.getRules().lookup ("TestApplyTaclet_wrap_blocks_two_empty_lists");
	TacletIndex tacletIndex = new TacletIndex ();
 	tacletIndex.add ( testApplyTaclet_wrap_blocks_two_empty_lists );
	Goal goal = createGoal ( proof[14].root(), tacletIndex );
	PosInOccurrence pos
	    = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
				  PosInTerm.getTopLevel(),
				  false);

 	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
	    getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);	

	assertTrue("Expected one rule application.",rApplist.size()==1);
	assertTrue("Rule App should be complete", rApplist.head().complete());

	// the bug was: the next method throws the exception
	// java.util.NoSuchElementException
 	ImmutableList<Goal> goals=rApplist.head ().execute(goal, TacletForTests.services());

	assertTrue("Expected one goal.",goals.size()==1);
	
	Sequent correctSeq = proof[15].root ().sequent ();	
	assertEquals("Wrong result", correctSeq, goals.head().sequent());
    }

    public void testCatchList () {
	doTestCatchList ( 16 );
	doTestCatchList ( 18 );
	doTestCatchList ( 20 );
    }


    private void doTestCatchList ( int p_proof ) {
	NoPosTacletApp test_catch_list0 =
	    TacletForTests.getRules().lookup ("test_catch_list0");
	NoPosTacletApp test_catch_list1 =
	    TacletForTests.getRules().lookup ("test_catch_list1");
	TacletIndex tacletIndex = new TacletIndex ();
 	tacletIndex.add ( test_catch_list0 );
 	tacletIndex.add ( test_catch_list1 );
	Goal goal = createGoal ( proof[p_proof].root(), tacletIndex );
	PosInOccurrence pos
	    = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
				  PosInTerm.getTopLevel(),
				  false);

 	ImmutableList<TacletApp> rApplist = goal.ruleAppIndex().
	    getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);	

	assertTrue("Expected one rule application.", rApplist.size()==1);
	assertTrue("Rule App should be complete.", rApplist.head().complete());

 	ImmutableList<Goal> goals=rApplist.head ().execute(goal, TacletForTests.services());

	assertTrue("Expected one goal.", goals.size()==1);
	
	Sequent correctSeq = proof[p_proof+1].root ().sequent ();

	Term resultFormula  = goals.head().sequent().getFormulabyNr ( 1 ).formula ();
	Term correctFormula = correctSeq.getFormulabyNr ( 1 ).formula ();

	assertTrue("Wrong result", resultFormula.equalsModRenaming ( correctFormula ) );
    }

    private Goal createGoal ( Node n, TacletIndex tacletIndex ) {
	final BuiltInRuleAppIndex birIndex = new BuiltInRuleAppIndex
	    ( new BuiltInRuleIndex () );
	final RuleAppIndex ruleAppIndex = new RuleAppIndex
	    ( tacletIndex, birIndex, n.proof().getServices() );
	final Goal goal = new Goal ( n, ruleAppIndex );
	return goal;
    }

    /**
     * tests if the variable sv collector pays attention to schema variables 
     * occuring as part of attributes and/or updates (there was a bug where 
     * this has been forgotten, and as a result after applying a method contract
     * schemavariables have been introduces into a goal sequent)
     */
    public void testTacletVariableCollector () {
        TacletSchemaVariableCollector coll = new TacletSchemaVariableCollector();
        Taclet t = TacletForTests.getRules ().lookup ( "testUninstantiatedSVCollector" ).taclet();
        coll.visit(t, false);
        ImmutableSet<SchemaVariable> collSet = DefaultImmutableSet.<SchemaVariable>nil();
        Iterator<SchemaVariable> it = coll.varIterator();
        while (it.hasNext()) {
            SchemaVariable sv = it.next();
            collSet = collSet.add(sv);
        }
        
        assertTrue("Expected four uninstantiated variables in taclet " +
                   t +", but found " + collSet.size(), collSet.size()==4);              
    }
    
    /**
     * tests a bug, which caused the first statement in a context block to be discarded  
     * in cases where the complete program has been matched by the prefix and suffix of the context 
     * block i.e.
     * a rule like
     * <code>
     * \find ( <.. ...>\forall u; post )
     * \replacewith (\forall u;<.. ..>post)      
     * </code>
     * applied on 
     * <code> < method-frame():{ while (...) {...} } >\forall int i; i>0</code>
     * created the goal
     * <code> \forall int i;< method-frame():{ } >i>0 </code>
     * which is of course incorrect.
     */
    
    public void testCompleteContextAddBug() {
        NoPosTacletApp app = TacletForTests.getRules ().lookup ( "TestApplyTaclet_allPullOutBehindDiamond" );

        TacletIndex tacletIndex = new TacletIndex ();
        tacletIndex.add ( app );
        Goal goal = createGoal ( proof[22].root(), tacletIndex );
        PosInOccurrence pos
            = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
                                  PosInTerm.getTopLevel(),
                                  false);

        ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
            getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);    

        assertTrue("Expected one rule application.",rApplist.size()==1);
        assertTrue("Rule App should be complete", rApplist.head().complete());
      
        ImmutableList<Goal> goals=rApplist.head ().execute(goal, TacletForTests.services());
        
        assertTrue("Expected one goal.",goals.size()==1);
        
        // the content of the diamond must not have changed 
        ProgramElement expected = proof[22].root().sequent().getFormulabyNr(1).formula().javaBlock().program();
        ProgramElement is = goals.head().sequent().getFormulabyNr(1).formula().sub(0).javaBlock().program();
        assertEquals("Context has been thrown away.",expected, is);
       
    }
    
    /**
     *  
     */
    public void testContextAdding() {
        NoPosTacletApp app = TacletForTests.getRules ().lookup ( "TestApplyTaclet_addEmptyStatement" );

        TacletIndex tacletIndex = new TacletIndex ();
        tacletIndex.add ( app );
        Goal goal = createGoal ( proof[22].root(), tacletIndex );
        PosInOccurrence pos
            = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
                                  PosInTerm.getTopLevel(),
                                  false);

        ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
            getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);    

        assertTrue("Expected one rule application.",rApplist.size()==1);
        assertTrue("Rule App should be complete", rApplist.head().complete());
      
        ImmutableList<Goal> goals=rApplist.head ().execute(goal, TacletForTests.services());
        
        assertTrue("Expected one goal.",goals.size()==1);
        
        // the content of the diamond must not have changed 
        ProgramElement expected = TacletForTests.parsePrg("{try{ ; while (1==1) {if (1==2) {break;}} return 1==3; " +
                        "int i=17; } catch (Exception e) { return null;}}");
                        
        ProgramElement is = goals.head().sequent().getFormulabyNr(1).formula().javaBlock().program();
        assertTrue("Expected:"+expected+"\n but was:"+is, expected.equalsModRenaming(is, new NameAbstractionTable()));      
    }
    
    /**
     *  this test is different from the other empty block removal test
     */
    public void testRemoveEmptyBlock() {
        NoPosTacletApp app = TacletForTests.getRules ().lookup ( "TestApplyTaclet_removeEmptyBlock" );

        TacletIndex tacletIndex = new TacletIndex ();
        tacletIndex.add ( app );
        Goal goal = createGoal ( proof[23].root(), tacletIndex );
        PosInOccurrence pos
            = new PosInOccurrence(goal.sequent().succedent().getFirst(), 
                                  PosInTerm.getTopLevel(),
                                  false);

        ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
            getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);    

        assertTrue("Expected one rule application.",rApplist.size()==1);
        assertTrue("Rule App should be complete", rApplist.head().complete());
      
        ImmutableList<Goal> goals=rApplist.head ().execute(goal, TacletForTests.services());
        
        assertTrue("Expected one goal.",goals.size()==1);
        
        // the content of the diamond must not have changed 
        ProgramElement expected = TacletForTests.parsePrg("{try{while (1==1) {if (1==2) {break;}} return 1==3; " +
                        "int i=17; } catch (Exception e) { return null;}}");
        
        ProgramElement is = goals.head().sequent().getFormulabyNr(1).formula().javaBlock().program();
        assertTrue("Expected:"+expected+"\n but was:"+is, expected.equalsModRenaming(is, new NameAbstractionTable()));
    }
    
}