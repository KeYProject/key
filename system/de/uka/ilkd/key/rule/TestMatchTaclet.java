// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/**
 * tests if match checks the variable conditions in Taclets. 
 */
package de.uka.ilkd.key.rule;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.ArrayOfProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ClassInstanceSortImpl;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.IHTacletFilter;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.util.Debug;


public class TestMatchTaclet extends TestCase {
    FindTaclet if_addrule_conflict;
    FindTaclet find_addrule_conflict;
    FindTaclet if_find_clash;
    FindTaclet if_add_no_clash;
    FindTaclet not_free_conflict;
    FindTaclet all_left;
    FindTaclet assign_n;
    TacletApp close_rule;
    Term matchExc;
    Taclet[] conflict;
    Services services;
    
    public TestMatchTaclet(String name) {
	super(name);
    }

    public TestMatchTaclet(String name, boolean b) {
	super(name);
	Debug.ENABLE_DEBUG = b;
    }

    public void setUp() {
        TacletForTests.setStandardFile(System.getProperty("key.home")
                + java.io.File.separator + "system" + java.io.File.separator
                + "de/uka/ilkd/key/logic/testRuleMatch.txt");
        TacletForTests.parse();
    
        services = TacletForTests.services();
        
        all_left = (FindTaclet) TacletForTests.getTaclet(
                "TestMatchTaclet_for_all").taclet();
        if_addrule_conflict = (FindTaclet) TacletForTests.getTaclet(
                "if_addrule_clash").taclet();

        find_addrule_conflict = (FindTaclet) TacletForTests.getTaclet(
                "find_addrule_clash").taclet();

        if_find_clash = (FindTaclet) TacletForTests.getTaclet("if_find_clash")
                .taclet();

        if_add_no_clash = (FindTaclet) TacletForTests.getTaclet(
                "if_add_no_clash").taclet();

        not_free_conflict = (FindTaclet) TacletForTests.getTaclet(
                "not_free_conflict").taclet();
        close_rule = TacletForTests.getTaclet("close_rule");

        conflict = new Taclet[4];
        conflict[0] = (FindTaclet) TacletForTests.getTaclet("test_rule_one")
                .taclet();
        conflict[1] = (FindTaclet) TacletForTests.getTaclet("test_rule_two")
                .taclet();
        conflict[2] = (FindTaclet) TacletForTests.getTaclet("test_rule_three")
                .taclet();
        conflict[3] = (FindTaclet) TacletForTests.getTaclet("test_rule_four")
                .taclet();

        assign_n = (FindTaclet) TacletForTests.getTaclet(
                "TestMatchTaclet_assign_n").taclet();

    }
    
    public void tearDown() {
        if_addrule_conflict = null;
        find_addrule_conflict = null;
        if_find_clash = null;
        if_add_no_clash = null;
        not_free_conflict = null;
        all_left = null;
        assign_n = null;
        close_rule = null;
        matchExc = null;
        conflict = null;
        services = null;
    }
    
    public void testStatementListMatch() {
	Term match = TacletForTests.parseTerm("\\<{ l1:{l2:{while (true) {break; "
					      +"int k=1; {int j = 1; j++;} int c = 56;}}} }\\> true");

	FindTaclet break_while =  (FindTaclet)TacletForTests
	    .getTaclet("TestMatchTaclet_break_while").taclet();   
	
	MatchConditions svi = break_while.matchJavaBlock
	    (match, (Term) break_while.find(), 
	     MatchConditions.EMPTY_MATCHCONDITIONS, 
	     services);
	
	assertNotNull("Matches have been expected.", svi);

	SchemaVariable sv = TacletForTests.svLookup("#stmnt_list");
	assertTrue("Expected list of statement to be instantiated.",
		   svi.getInstantiations().isInstantiated(sv));
	assertTrue("The three statements behind the break should be matched.",
		   ((ArrayOfProgramElement)svi.getInstantiations().getInstantiation(sv)).size() == 3);
    }

    public void testProgramMatch0() {
	Term match = TacletForTests.parseTerm("\\<{ l1:{l2:{while (true) {break;} "
					      +"int k=1;}} }\\> true");
	FindTaclet taclet=(FindTaclet)TacletForTests
	    .getTaclet("TestMatchTaclet_whileright").taclet();   
	MatchConditions svi = taclet.matchJavaBlock
	    (match, (Term) taclet.find(),
	     MatchConditions.EMPTY_MATCHCONDITIONS, services); 

	assertNotNull("There should be instantiations",svi);
	assertTrue("#e2 should be instantiated",
		   svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#e2")));
	assertTrue("#p1 should be instantiated",
		   svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#p1")));
	
	Term matchTwo = TacletForTests.parseTerm("\\<{ l1:{l2:{while (true) {boolean b=true; break;} "
						 +"}int k=1;} }\\> true");
	FindTaclet tacletTwo=(FindTaclet)TacletForTests
	    .getTaclet("TestMatchTaclet_whileright_labeled").taclet(); 
	
	svi = tacletTwo.matchJavaBlock
	       (matchTwo, (Term) tacletTwo.find(),
		MatchConditions.EMPTY_MATCHCONDITIONS, services); 
	assertNotNull(svi);

	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#e2")));
	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#p1")));
	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#lab")));

	Term match3 = TacletForTests.parseTerm("\\<{ l1:{l2:{while (true) {boolean b=false; break;} "
					       +"int k=1;}} }\\> true");
	FindTaclet taclet3=(FindTaclet)TacletForTests
	    .getTaclet("TestMatchTaclet_whileright_labeled").taclet(); 
	
	svi = taclet3.matchJavaBlock
	       (match3, (Term) taclet3.find(),
		MatchConditions.EMPTY_MATCHCONDITIONS, services); 
	assertNull(svi);

	Term emptyBlock = 
	    TacletForTests.parseTerm("\\<{ { {} int i = 0; } }\\> true");
	FindTaclet empty_block_taclet=(FindTaclet)TacletForTests
	    .getTaclet("TestMatchTaclet_empty_block").taclet(); 
	
 	svi = empty_block_taclet.matchJavaBlock
	       (emptyBlock, (Term) empty_block_taclet.find(),
		MatchConditions.EMPTY_MATCHCONDITIONS, services); 
 	assertTrue(svi != null);

	Term emptyBlock2 = 
	    TacletForTests.parseTerm("\\<{ { {} } }\\> true");

 	svi = empty_block_taclet.matchJavaBlock
	       (emptyBlock2, (Term) empty_block_taclet.find(),
		MatchConditions.EMPTY_MATCHCONDITIONS, services); 

	assertNotNull(svi);

	Debug.out("%%%%%%%%%%%%");
	Term emptyBlock3 = 
	    TacletForTests.parseTerm("\\<{ { {} l1:{} } }\\> true");
 	svi = empty_block_taclet.matchJavaBlock
	       (emptyBlock3, (Term) empty_block_taclet.find(),
		MatchConditions.EMPTY_MATCHCONDITIONS, services); 
	assertNotNull(svi);


	FindTaclet var_decl_taclet=(FindTaclet)TacletForTests
	    .getTaclet("TestMatchTaclet_variable_declaration").taclet(); 

	svi = var_decl_taclet.matchJavaBlock
	    (emptyBlock, (Term) var_decl_taclet.find(),
	     MatchConditions.EMPTY_MATCHCONDITIONS, services); 
	assertNull(svi);	

	Term emptyLabel = 
	    TacletForTests.parseTerm("\\<{ { l1:{} } }\\> true");
	FindTaclet empty_label_taclet=(FindTaclet)TacletForTests
	    .getTaclet("TestMatchTaclet_empty_label").taclet(); 
	svi = empty_label_taclet.matchJavaBlock
	    (emptyLabel, 
	     (Term)empty_label_taclet.find(),
	     MatchConditions.EMPTY_MATCHCONDITIONS, services); 
	assertNotNull(svi);

	Term emptyLabel2 = 
	    TacletForTests.parseTerm("\\<{ l2:{ l1:{} } }\\> true");
	svi = empty_label_taclet.matchJavaBlock
	       (emptyLabel2, 
		(Term)empty_label_taclet.find(),
		MatchConditions.EMPTY_MATCHCONDITIONS, services); 
	assertNotNull(svi);

	Term emptyLabel3 = 
	    TacletForTests.parseTerm("\\<{ {l3:{{l2:{l1:{}}}} int i = 0;} }\\> true");
	svi = empty_label_taclet.matchJavaBlock
	       (emptyLabel3, 
		(Term)empty_label_taclet.find(),
		MatchConditions.EMPTY_MATCHCONDITIONS, services); 
	assertNotNull(svi);
    }

        
    public void testProgramMatch1() {
	Services services = TacletForTests.services();
	de.uka.ilkd.key.java.Recoder2KeY c2k
	    = new de.uka.ilkd.key.java.Recoder2KeY(services,
						  new NamespaceSet());
	JavaBlock jb=c2k.readBlock("{ int i; int j; i=++j;"
				   +" while(true) {break;}}", 
				   c2k.createEmptyContext());

	de.uka.ilkd.key.java.StatementBlock sb
	    =(de.uka.ilkd.key.java.StatementBlock)jb.program();

	JavaBlock javaBlock = JavaBlock.createJavaBlock
	    (new de.uka.ilkd.key.java.StatementBlock
		(new de.uka.ilkd.key.java.ArrayOfStatement
		    (new de.uka.ilkd.key.java.Statement[]{
			(de.uka.ilkd.key.java.Statement)sb.getChildAt(2),
			(de.uka.ilkd.key.java.Statement)sb.getChildAt(3)
		    })));


	Term match = TermFactory.DEFAULT.createDiamondTerm
	    (javaBlock, TermFactory.DEFAULT.createJunctorTerm(Junctor.TRUE));
	
	FindTaclet taclet=(FindTaclet)TacletForTests
	    .getTaclet("TestMatchTaclet_preincrement").taclet();   

	MatchConditions svi =
	    taclet.matchJavaBlock
	    (match, (Term)taclet.find(), 
	     MatchConditions.EMPTY_MATCHCONDITIONS, services); 


	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#slhs1")));
	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#slhs2")));
    }
    
    public void testProgramMatch2() {
	Term match = TacletForTests.parseTerm("\\<{int i; int k;}\\>(\\<{for (int i=0;"
					      +" i<2; i++) {break;} "
					      +"int k=1; }\\> true)");
	FindTaclet taclet
	    =(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_for_right").taclet();   
	MatchConditions svi = taclet.matchJavaBlock
	    (match.sub(0), (Term)taclet.find(), 
	     MatchConditions.EMPTY_MATCHCONDITIONS, services); 


	assertNotNull(svi);
	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#loopInit")));
	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#guard")));
	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#forupdates")));
	assertTrue(svi.getInstantiations().isInstantiated(TacletForTests
				      .svLookup("#p1")));
    }
    /*
      public void testProgramMatch3() {
      Term match = TacletForTests.parseTerm("<{ {int i=0; break; }  }> true");
      FindTaclet taclet
      =(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_local_variable_rename").taclet();   
      SVInstantiations svi=(taclet.matchJavaProgram
      (match.javaBlock(), 
      (ContextStatementBlock)taclet.find().javaBlock().program(), 
      taclet.createInitialInstantiation())); 

      System.out.println(svi);
      }
    */
        
    public void testProgramMatch4() {
	Term match = TacletForTests.parseTerm
	    ("\\<{{while (1==1) {if (1==2) {break;}} return 1==3;}}\\>A");

	FindTaclet taclet
	    =(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_while0").taclet();   

	MatchConditions mc=(taclet.match
			    (match, 
			     taclet.find(), 
			     MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 
	assertNotNull(mc);
    }


    public void testVarOccursInIfAndAddRule() {

	Term match = TacletForTests.parseTerm("\\forall testSort z; (p(z) -> A)");
	assertTrue(match.arity() == 1);
	
	// test at the subformula p(z) -> A that has a free variable
	// therefore no match should be found

	Sequent seq = Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert
	     (0, new ConstrainedFormula(match.sub(0), 
					Constraint.BOTTOM)).semisequent(), 
	     Semisequent.EMPTY_SEMISEQUENT);

	assertTrue("An area conflict should happen because there is a free"+
		   " variable and the matching part is in the if and addrule", 
		   NoPosTacletApp.createNoPosTacletApp ( if_addrule_conflict )
		   .findIfFormulaInstantiations ( seq, services, Constraint.BOTTOM ).size() == 0);
	       
 	// we bind the free variable now a match should be found
	seq = Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new ConstrainedFormula
		(match, 
		 Constraint.BOTTOM)).semisequent(), 
	     Semisequent.EMPTY_SEMISEQUENT );

	assertTrue("No area conflict should happen because all variables are bound.", 
		   NoPosTacletApp.createNoPosTacletApp ( if_addrule_conflict )
		   .findIfFormulaInstantiations ( seq, services, Constraint.BOTTOM ).size() != 0);
    }


    public void testVarOccursInFindAndAddRule() {
	Term match = TacletForTests.parseTerm("\\forall testSort z; (p(z) -> A)");

    
	//seq contains term that can match but has a free variable, so
	//matching to a should be not possible

	PosTacletApp app = PosTacletApp.createPosTacletApp
	((FindTaclet)find_addrule_conflict,
	        find_addrule_conflict.match(match.sub(0), 
	                find_addrule_conflict.find(), false,
	                MatchConditions.EMPTY_MATCHCONDITIONS, services, 
	                Constraint.BOTTOM).getInstantiations(),
                    new PosInOccurrence(new ConstrainedFormula(match),
                            PosInTerm.TOP_LEVEL.down(0), true));
        
    
	assertTrue("A match has been found but there is a free variable in"+
		   " the term that has been matched and therefore an area"+
		   " conflict with find and addrule should have happened.",
		    app == null);

	// var is not free, match should be found 
	app = PosTacletApp.createPosTacletApp
	((FindTaclet)find_addrule_conflict,
            find_addrule_conflict.match(match, 
                    find_addrule_conflict.find(), false,
                    MatchConditions.EMPTY_MATCHCONDITIONS, services, 
                    Constraint.BOTTOM).getInstantiations(),
                    new PosInOccurrence(new ConstrainedFormula(match),
                            PosInTerm.TOP_LEVEL, true));
	assertTrue("A match should have been found,"+
		   " because here there formerly free variable is bound.",
		   app != null);	           
    }



    public void testRWVarOccursFindAndIf() {
	// the find expression is not a sequent, therefore find and if
	// are two different areas and if find matches a term that
	// contains a free variable, no match should be possible  
	//seq contains term that can match but has a free variable, so
	//matching to a should be not possible
	Term match = TacletForTests.parseTerm("\\forall testSort z; (p(z) -> A)");
	TacletApp app = PosTacletApp.createPosTacletApp
	(if_find_clash,
            if_find_clash.match(match.sub(0), if_find_clash.find(), false, 
               MatchConditions.EMPTY_MATCHCONDITIONS, 
               services, Constraint.BOTTOM).getInstantiations(),
               new PosInOccurrence(new ConstrainedFormula(match.sub(0)),
                       PosInTerm.TOP_LEVEL.down(0), true));
        
	assertTrue("Match found but match term contains free var and"+
		   "matching var occurs in two instantiation areas"+
		   " (if and find)", app == null); 


	assertTrue("Match not found", 
		   if_find_clash.match(match, if_find_clash.find(), false,
				       MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM) != null);	           
    }

    public void testRWVarOccursInAddAndIf() {
	// no clash should happen because in this case the add and if
	// sections are the same area
	Term match = TacletForTests.parseTerm("\\forall testSort z; (p(z) -> A)");

	assertTrue("Match not found but should exist"+
		   " because add and if are same area",
                   if_add_no_clash.match(match.sub(0), if_add_no_clash.find(), false,
					 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM) != null); 
    }
    

    
    public void testXNotFreeInYConflict() {
	Term free_in = TacletForTests.parseTerm("\\forall testSort z; (p(z) & p(f(z)))");
	// matching the not_free_conflict Taclet with (P(f(z),z) should
	// result in a conflict, because z is free in f(z) but
	// the Taclet demands z not free in f(z)
	assertTrue("Match should not be found because of conflict with "+
		   "..not free in..", NoPosTacletApp.createNoPosTacletApp
		   (not_free_conflict,
		    not_free_conflict.match
		    (free_in, not_free_conflict.find(), false,
		     MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)) == null);

	Term not_free_in = TacletForTests.parseTerm("\\forall testSort z; (p(z) & p(c))");
 	assertTrue("Match should be found because .. not free in.. "+
		   "is not relevant", NoPosTacletApp.createNoPosTacletApp
		   (not_free_conflict,
		    not_free_conflict.match
		    (not_free_in, not_free_conflict.find(), false,
		     MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)) != null);
    }


    public void testCloseWithBoundRenaming() {
	Term closeable_one = TacletForTests.parseTerm("\\forall testSort z; p(z)");
	Term closeable_two = TacletForTests.parseTerm("\\forall testSort y; p(y)");
	Sequent seq = Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert
	     (0, new ConstrainedFormula(closeable_one)).semisequent(), 
	     Semisequent.EMPTY_SEMISEQUENT.insert
	     (0, new ConstrainedFormula(closeable_two)).semisequent()); 	
	TacletIndex index = new TacletIndex();
	index.add(close_rule.taclet());
        PosInOccurrence posAntec = new PosInOccurrence(new ConstrainedFormula(closeable_two, Constraint.BOTTOM),
                PosInTerm.TOP_LEVEL, false);

	TacletApp tacletApp = index.getSuccedentTaclet(posAntec,
	                                               new IHTacletFilter (true, SLListOfRuleSet.EMPTY_LIST),
	                                               services, Constraint.BOTTOM).iterator().next();
	assertTrue("Match should be possible(modulo renaming)",
		   tacletApp.findIfFormulaInstantiations ( seq, services, Constraint.BOTTOM ).size()>0);
    }
   
    // a greater test 
    public void testConflict() {
	Term match = TacletForTests.parseTerm("p1(m1(n))");
	for (int i=0; i<conflict.length; i++) {
	    assertTrue("Match should not be found because of area conflict:"+i,
		       conflict[i].match
		       (match, ((FindTaclet)conflict[i]).find(), 
			MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)==null);	    
	}
    }
    
    // test match of update terms
    public void testUpdateMatch() {           
	Term match = TacletForTests.parseTerm("\\<{int i;}\\>{i:=(jint)2}(\\forall nat z; (q1(z)))");
	match = match.sub(0);
	assertTrue("Instantiations should be found as updates can be ignored if "+
		   "only the term that is matched has an update and the "+
		   "template it is matched to has none.",
		   all_left.match(match, ((FindTaclet)all_left).find(), 
				  true, MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)!=null);
		
	Term match2 = TacletForTests.parseTerm("\\<{int i;}\\>{i:=(jint)Z(2(#))} true");
	match2 = match2.sub(0);
	assertTrue("Instantiations should be found.",
		   assign_n.match(match2, ((FindTaclet)assign_n).find(), 
				  true, MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)!=null);
    }


    public void testProgramMatchEmptyBlock() {
	Term match = TacletForTests.parseTerm("\\<{ }\\>true ");
	FindTaclet taclet
	    =(FindTaclet)TacletForTests.getTaclet("empty_diamond").taclet();   
	MatchConditions mc=(taclet.match
			    (match, 
			     taclet.find(), 
			     MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 

	assertNotNull(mc);

	match = TacletForTests.parseTerm("\\<{ {} }\\>true ");
	taclet=(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_empty_block").taclet();   

	mc=(taclet.match(match, 
			 taclet.find(), 
			 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 

	assertNotNull(mc);

	match = TacletForTests.parseTerm("\\<{ {int i = 0;} }\\>true ");
	mc=(taclet.match(match, 
			 taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 

	assertNull("The block is not empty",mc);

    }

    //Assume A is a supersort of B. Then a term SV of sort A should match
    //a term of sort B. (assertNotNull)
    public void testWithSubSortsTermSV() {
	Sort osort1=(Sort)TacletForTests.getSorts().lookup(new Name("Obj"));
	Sort osort2=new ClassInstanceSortImpl(new Name("os2"), osort1, false);
	Sort osort3=new ClassInstanceSortImpl(new Name("os3"), osort1, false);
	Sort osort4=new ClassInstanceSortImpl(new Name("os4"), 
					      SetAsListOfSort.EMPTY_SET
					      .add(osort2).add(osort3), false);
	Function v4=new Function(new Name("v4"), osort4, new Sort[0]);	
	TermFactory tf=TermFactory.DEFAULT;
	Term match=tf.createFunctionTerm(v4);
	FindTaclet taclet=(FindTaclet)TacletForTests.getTaclet
	    ("TestMatchTaclet_subsort_termSV").taclet();   
	MatchConditions mc=taclet.match(match, 
					taclet.find(), 
					MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM);
	assertNotNull(mc);
    }

    //Assume A is a supersort of B. Then a variable SV of sort A should _NOT_
    //match a logic variable of sort B. (assertNull)
    public void testWithSubSortsVariableSV() {
	Sort osort1=(Sort)TacletForTests.getSorts().lookup(new Name("Obj"));
	Sort osort2=new ClassInstanceSortImpl(new Name("os2"), osort1, false);
	Sort osort3=new ClassInstanceSortImpl(new Name("os3"), osort1, false);
	Sort osort4=new ClassInstanceSortImpl(new Name("os4"), 
					      SetAsListOfSort.EMPTY_SET
					      .add(osort2).add(osort3), false);	
	TermFactory tf=TermFactory.DEFAULT;
	Function aPred = (Function)TacletForTests.getFunctions().lookup(new Name("A"));
	Term sub = tf.createFunctionTerm(aPred);
	Term match=tf.createQuantifierTerm(Quantifier.ALL, 
					   new LogicVariable(new Name("lv"), osort4), 
					   sub);
	FindTaclet taclet=(FindTaclet)TacletForTests.getTaclet
	    ("TestMatchTaclet_subsort_variableSV").taclet();   
	MatchConditions mc=taclet.match(match, 
					taclet.find(), 
					MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM);
	assertNull(mc);
    }

    public void testNoContextMatching() {
	Term match = TacletForTests.parseTerm("\\<{{ int i = 0;}}\\>true ");
	FindTaclet taclet=(FindTaclet)TacletForTests.getTaclet
	    ("TestMatchTaclet_nocontext").taclet();   
	MatchConditions mc=(taclet.match(match, 
					 taclet.find(), 
					 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 
	assertNotNull("No context matching corrupt.", mc);
    }

    public void testPrefixMatching() {
	TermFactory tf=TermFactory.DEFAULT;
	Term match = TacletForTests.parseTerm("\\<{return;}\\>true ");
	StatementBlock prg = (StatementBlock)match.javaBlock().program();
	ExecutionContext ec = new ExecutionContext
	    (new TypeRef(new KeYJavaType
		(PrimitiveType.JAVA_BYTE, 
		 new PrimitiveSort(new Name("byte")))),
	     new LocationVariable(new ProgramElementName("testVar"),
				 new PrimitiveSort(new Name("testSort"))));
	MethodFrame mframe = new MethodFrame(null, ec, prg);
	match = tf.createDiamondTerm
	    (JavaBlock.createJavaBlock(new StatementBlock(mframe)), 
	     match.sub(0));
	FindTaclet taclet=(FindTaclet)TacletForTests.getTaclet
	    ("TestMatchTaclet_methodframe").taclet();
	MatchConditions mc = (taclet.match(match, 
					   taclet.find(), 
					   MatchConditions.EMPTY_MATCHCONDITIONS,
					   services, Constraint.BOTTOM));
	assertNotNull("Method-Frame should match", mc);

	Term termWithPV=TacletForTests.parseTerm("\\<{int i;}\\>i=0");
	match = TacletForTests.parseTerm("\\<{return 2;}\\>true ");
	prg = (StatementBlock)match.javaBlock().program();
	mframe = new MethodFrame((IProgramVariable)termWithPV.sub(0).sub(0).op(),
				  ec, prg);
	match = tf.createDiamondTerm(JavaBlock.createJavaBlock(new StatementBlock(mframe)), match.sub(0));
	taclet=(FindTaclet)TacletForTests.getTaclet
	    ("TestMatchTaclet_methodframe_value").taclet();	
	mc=(taclet.match(match, 
			 taclet.find(), 
			 MatchConditions.EMPTY_MATCHCONDITIONS,
			 services, Constraint.BOTTOM));
	assertNotNull("Method-Frame with return value should match",mc);

    }

    public void testBugsThathaveBeenRemoved() {

	Term match = TacletForTests.parseTerm("\\<{ int i = 0; }\\>true ");
	FindTaclet taclet=(FindTaclet)TacletForTests.getTaclet
	    ("TestMatchTaclet_eliminate_variable_declaration").taclet();   
	MatchConditions mc=(taclet.match(match, 
					 taclet.find(), 
					 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 

 	assertNull("The reason for this bug was related to the introduction of "+
 		   "statementlist schemavariables and that we could not end the "+ 
 		   "match if the size of nonterminalelements was unequal "+
 		   "The solution was to weaken the check for statement blocks but NOT "+
 		   "for other statement or expressions containers. The bug occured because "+
 		   "the weaker test was also "+
 		   "performed for expressions.", mc);

 	match = TacletForTests.parseTerm("\\<{ {{throw null;} int i = 0;} }\\>true ");
 	taclet=(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_throw_in_block").taclet();   
 	mc=(taclet.match(match, 
			 taclet.find(), 
			 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 
 	assertNull("No match expected.", mc);

 	match = TacletForTests.parseTerm
 	    ("\\<{{ int l1=1;} if (true);}\\>true");
 	taclet=(FindTaclet)TacletForTests.getTaclet
 	    ("TestMatchTaclet_elim_double_block").taclet();   
 	mc=(taclet.match(match, 
 			 taclet.find(), 
 			 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM));
 	assertNull("Removed bug #118. No match expected.", mc);

 	match = TacletForTests.parseTerm("\\<{ {} {int i;} }\\> true");
 	taclet=(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_wrap_blocks").taclet();   
 	mc=(taclet.match(match, 
 			 taclet.find(), 
 			 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 
 	assertNotNull("Bug originally failed to match the first empty block.", mc);

 	match = TacletForTests.parseTerm("\\<{ {} {int i;} }\\> true");
 	taclet=(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_wrap_blocks_two_empty_lists").taclet();   
 	mc=(taclet.match(match, 
 			 taclet.find(), 
 			 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 
 	assertNotNull("Bug originally failed to match the first empty block,"+
 		      " because of he was not able to match two succeeding empty lists.", mc);

	match = TacletForTests.parseTerm("\\<{ {{}} {} }\\> true");
	taclet=(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_remove_empty_blocks").taclet();   
	mc=(taclet.match(match, 
			 taclet.find(), 
			 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 
	assertNotNull("Bug matching empty blocks using list svs.", mc);

	match = TacletForTests.parseTerm("\\<{ { int i; } {} }\\> true");
	taclet=(FindTaclet)TacletForTests.getTaclet("TestMatchTaclet_bug_matching_lists").taclet();   
	mc=(taclet.match(match, 
			 taclet.find(), 
			 MatchConditions.EMPTY_MATCHCONDITIONS, services, Constraint.BOTTOM)); 
	assertNotNull("List matching bug.", mc);
	
    }

    public static void main(String args[]) {
	TestMatchTaclet t=new TestMatchTaclet("XXX", true);
	t.setUp();
	t.testPrefixMatching();	
	//	t.testBugsThathaveBeenRemoved();
	//t.testStatementListMatch();
    }
    
}
