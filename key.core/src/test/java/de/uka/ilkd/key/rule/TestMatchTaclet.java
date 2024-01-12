/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.io.File;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.TacletIndexKit;
import de.uka.ilkd.key.proof.rulefilter.IHTacletFilter;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


/**
 * tests if match checks the variable conditions in Taclets.
 */
public class TestMatchTaclet {

    private static TermBuilder TB;

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


    @BeforeEach
    public void setUp() {
        File ruleFile = new File(
            HelperClassForTests.TESTCASE_DIRECTORY + "/../de/uka/ilkd/key/rule/testRuleMatch.txt");
        assertTrue(ruleFile.exists(), "File '" + ruleFile + "' does not exist.");
        TacletForTests.setStandardFile(ruleFile.getAbsolutePath());
        TacletForTests.parse();

        services = TacletForTests.services();
        TB = services.getTermBuilder();

        all_left = (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_for_all").taclet();
        if_addrule_conflict = (FindTaclet) TacletForTests.getTaclet("if_addrule_clash").taclet();

        find_addrule_conflict =
            (FindTaclet) TacletForTests.getTaclet("find_addrule_clash").taclet();

        if_find_clash = (FindTaclet) TacletForTests.getTaclet("if_find_clash").taclet();

        if_add_no_clash = (FindTaclet) TacletForTests.getTaclet("if_add_no_clash").taclet();

        not_free_conflict = (FindTaclet) TacletForTests.getTaclet("not_free_conflict").taclet();
        close_rule = TacletForTests.getTaclet("close_rule");

        conflict = new Taclet[4];
        conflict[0] = TacletForTests.getTaclet("test_rule_one").taclet();
        conflict[1] = TacletForTests.getTaclet("test_rule_two").taclet();
        conflict[2] = TacletForTests.getTaclet("test_rule_three").taclet();
        conflict[3] = TacletForTests.getTaclet("test_rule_four").taclet();

        assign_n = (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_assign_n").taclet();

    }

    @AfterEach
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


    @Test
    public void testProgramMatch4() {
        Term match =
            TacletForTests.parseTerm("\\<{{while (1==1) {if (1==2) {break;}} return 1==3;}}\\>A");

        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_while0").taclet();

        MatchConditions mc =
            (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services));
        assertNotNull(mc);
    }


    @Test
    public void testVarOccursInIfAndAddRule() {

        Term match = TacletForTests.parseTerm("\\forall testSort z; (p(z) -> A)");
        assertEquals(1, match.arity());

        // test at the subformula p(z) -> A that has a free variable
        // therefore no match should be found

        Sequent seq = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(match.sub(0))).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);

        assertEquals(0,
            NoPosTacletApp.createNoPosTacletApp(if_addrule_conflict)
                    .findIfFormulaInstantiations(seq, services).size(),
            "An area conflict should happen because there is a free"
                + " variable and the matching part is in the if and addrule");

        // we bind the free variable now a match should be found
        seq = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(match)).semisequent(),
            Semisequent.EMPTY_SEMISEQUENT);

        assertNotEquals(0,
            NoPosTacletApp.createNoPosTacletApp(if_addrule_conflict)
                    .findIfFormulaInstantiations(seq, services).size(),
            "No area conflict should happen because all variables are bound.");
    }


    @Test
    public void testVarOccursInFindAndAddRule() {
        Term match = TacletForTests.parseTerm("\\forall testSort z; (p(z) -> A)");


        // seq contains term that can match but has a free variable, so
        // matching to a should be not possible

        PosTacletApp app = PosTacletApp.createPosTacletApp(find_addrule_conflict,
            find_addrule_conflict.getMatcher()
                    .matchFind(match.sub(0), MatchConditions.EMPTY_MATCHCONDITIONS, services)
                    .getInstantiations(),
            new PosInOccurrence(new SequentFormula(match), PosInTerm.getTopLevel().down(0), true),
            services);


        assertNull(app,
            "A match has been found but there is a free variable in"
                + " the term that has been matched and therefore an area"
                + " conflict with find and addrule should have happened.");

        // var is not free, match should be found
        app = PosTacletApp.createPosTacletApp(find_addrule_conflict,
            find_addrule_conflict.getMatcher()
                    .matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services)
                    .getInstantiations(),
            new PosInOccurrence(new SequentFormula(match), PosInTerm.getTopLevel(), true),
            services);
        assertNotNull(app, "A match should have been found,"
            + " because here there formerly free variable is bound.");
    }


    @Test
    public void testRWVarOccursFindAndIf() {
        // the find expression is not a sequent, therefore find and if
        // are two different areas and if find matches a term that
        // contains a free variable, no match should be possible
        // seq contains term that can match but has a free variable, so
        // matching to a should be not possible
        Term match = TacletForTests.parseTerm("\\forall testSort z; (p(z) -> A)");
        TacletApp app = PosTacletApp
                .createPosTacletApp(if_find_clash,
                    if_find_clash.getMatcher()
                            .matchFind(match.sub(0), MatchConditions.EMPTY_MATCHCONDITIONS,
                                services)
                            .getInstantiations(),
                    new PosInOccurrence(new SequentFormula(match.sub(0)),
                        PosInTerm.getTopLevel().down(0), true),
                    services);

        assertNull(app, "Match found but match term contains free var and"
            + "matching var occurs in two instantiation areas" + " (if and find)");


        assertNotNull(if_find_clash.getMatcher().matchFind(match,
            MatchConditions.EMPTY_MATCHCONDITIONS, services), "Match not found");
    }

    @Test
    public void testRWVarOccursInAddAndIf() {
        // no clash should happen because in this case the add and if
        // sections are the same area
        Term match = TacletForTests.parseTerm("\\forall testSort z; (p(z) -> A)");

        assertNotNull(
            if_add_no_clash.getMatcher().matchFind(match.sub(0),
                MatchConditions.EMPTY_MATCHCONDITIONS, services),
            "Match not found but should exist" + " because add and if are same area");
    }


    @Test
    public void testXNotFreeInYConflict() {
        Term free_in = TacletForTests.parseTerm("\\forall testSort z; (p(z) & p(f(z)))");
        // matching the not_free_conflict Taclet with (P(f(z),z) should
        // result in a conflict, because z is free in f(z) but
        // the Taclet demands z not free in f(z)
        assertNull(
            NoPosTacletApp.createNoPosTacletApp(not_free_conflict,
                not_free_conflict.getMatcher().matchFind(free_in,
                    MatchConditions.EMPTY_MATCHCONDITIONS, services),
                services),
            "Match should not be found because of conflict with " + "..not free in..");

        Term not_free_in = TacletForTests.parseTerm("\\forall testSort z; (p(z) & p(c))");
        assertNotNull(
            NoPosTacletApp.createNoPosTacletApp(not_free_conflict,
                not_free_conflict.getMatcher().matchFind(not_free_in,
                    MatchConditions.EMPTY_MATCHCONDITIONS, services),
                services),
            "Match should be found because .. not free in.. " + "is not relevant");
    }


    @Test
    public void testCloseWithBoundRenaming() {
        Term closeable_one = TacletForTests.parseTerm("\\forall testSort z; p(z)");
        Term closeable_two = TacletForTests.parseTerm("\\forall testSort y; p(y)");
        Sequent seq = Sequent.createSequent(
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(closeable_one))
                    .semisequent(),
            Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(closeable_two))
                    .semisequent());
        TacletIndex index = TacletIndexKit.getKit().createTacletIndex();
        index.add(close_rule.taclet());
        PosInOccurrence pio =
            new PosInOccurrence(new SequentFormula(closeable_two), PosInTerm.getTopLevel(), false);

        TacletApp tacletApp =
            index.getSuccedentTaclet(pio, new IHTacletFilter(true, ImmutableSLList.nil()), services)
                    .iterator().next();
        assertTrue(tacletApp.findIfFormulaInstantiations(seq, services).size() > 0,
            "Match should be possible(modulo renaming)");
    }

    // a greater test
    @Test
    public void testConflict() {
        Term match = TacletForTests.parseTerm("p1(m1(n))");
        for (int i = 0; i < conflict.length; i++) {
            assertNull(conflict[i].getMatcher().matchFind(match,
                MatchConditions.EMPTY_MATCHCONDITIONS, services),
                "Match should not be found because of area conflict:" + i);
        }
    }

    // test match of update terms
    @Test
    public void testUpdateMatch() {
        LocationVariable i = new LocationVariable(new ProgramElementName("i"),
            services.getJavaInfo().getKeYJavaType("int"));
        services.getNamespaces().programVariables().add(i);
        Term match = TacletForTests.parseTerm("\\<{}\\>{i:=2}(\\forall nat z; (q1(z)))");
        match = match.sub(0);
        assertNotNull(
            all_left.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services),
            "Instantiations should be found as updates can be ignored if "
                + "only the term that is matched has an update and the "
                + "template it is matched to has none.");

        Term match2 = TacletForTests.parseTerm("\\<{int i;}\\>{i:=Z(2(#))} true");
        match2 = match2.sub(0);
        assertNotNull(assign_n.getMatcher().matchFind(match2, MatchConditions.EMPTY_MATCHCONDITIONS,
            services), "Instantiations should be found.");
    }


    @Test
    public void testProgramMatchEmptyBlock() {
        Term match = TacletForTests.parseTerm("\\<{ }\\>true ");
        FindTaclet taclet = (FindTaclet) TacletForTests.getTaclet("empty_diamond").taclet();
        MatchConditions mc =
            (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services));

        assertNotNull(mc);

        match = TacletForTests.parseTerm("\\<{ {} }\\>true ");
        taclet = (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_empty_block").taclet();

        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));

        assertNotNull(mc);

        match = TacletForTests.parseTerm("\\<{ {int i = 0;} }\\>true ");
        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));

        assertNull(mc, "The block is not empty");

    }

    // Assume A is a supersort of B. Then a term SV of sort A should match
    // a term of sort B. (assertNotNull)
    @Test
    public void testWithSubSortsTermSV() {
        Sort osort1 = TacletForTests.getSorts().lookup(new Name("Obj"));
        Sort osort2 = new SortImpl(new Name("os2"), osort1);
        Sort osort3 = new SortImpl(new Name("os3"), osort1);
        Sort osort4 = new SortImpl(new Name("os4"),
            DefaultImmutableSet.<Sort>nil().add(osort2).add(osort3), false);
        Function v4 = new Function(new Name("v4"), osort4, new Sort[0]);
        Term match = TB.tf().createTerm(v4);
        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_subsort_termSV").taclet();
        MatchConditions mc =
            taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNotNull(mc);
    }

    // Assume A is a supersort of B. Then a variable SV of sort A should _NOT_
    // match a logic variable of sort B. (assertNull)
    @Test
    public void testWithSubSortsVariableSV() {
        Sort osort1 = TacletForTests.getSorts().lookup(new Name("Obj"));
        Sort osort2 = new SortImpl(new Name("os2"), osort1);
        Sort osort3 = new SortImpl(new Name("os3"), osort1);
        Sort osort4 = new SortImpl(new Name("os4"),
            DefaultImmutableSet.<Sort>nil().add(osort2).add(osort3), false);
        Function aPred = TacletForTests.getFunctions().lookup(new Name("A"));
        Term sub = TB.tf().createTerm(aPred);
        Term match = TB.all(new LogicVariable(new Name("lv"), osort4), sub);
        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_subsort_variableSV").taclet();
        MatchConditions mc =
            taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNull(mc);
    }

    @Test
    public void testNoContextMatching() {
        Term match = TacletForTests.parseTerm("\\<{{ int i = 0;}}\\>true ");
        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_nocontext").taclet();
        MatchConditions mc =
            (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services));
        assertNotNull(mc, "No context matching corrupt.");
    }

    @Test
    public void testPrefixMatching() {
        Term match = TacletForTests.parseTerm("\\<{return;}\\>true ");
        StatementBlock prg = (StatementBlock) match.javaBlock().program();
        ExecutionContext ec = new ExecutionContext(
            new TypeRef(new KeYJavaType(PrimitiveType.JAVA_BYTE, new SortImpl(new Name("byte")))),
            null, new LocationVariable(new ProgramElementName("testVar"),
                new SortImpl(new Name("testSort"))));
        MethodFrame mframe = new MethodFrame(null, ec, prg);
        match = TB.dia(JavaBlock.createJavaBlock(new StatementBlock(mframe)), match.sub(0));
        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_methodframe").taclet();
        MatchConditions mc =
            (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services));
        assertNotNull(mc, "Method-Frame should match");

        Term termWithPV = TacletForTests.parseTerm("\\<{int i;}\\>i=0");
        match = TacletForTests.parseTerm("\\<{return 2;}\\>true ");
        prg = (StatementBlock) match.javaBlock().program();
        mframe = new MethodFrame((IProgramVariable) termWithPV.sub(0).sub(0).op(), ec, prg);
        match = TB.dia(JavaBlock.createJavaBlock(new StatementBlock(mframe)), match.sub(0));
        taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_methodframe_value").taclet();
        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));
        assertNotNull(mc, "Method-Frame with return value should match");

    }

    @Test
    public void testBugsThathaveBeenRemoved() {

        Term match = TacletForTests.parseTerm("\\<{ int i = 0; }\\>true ");
        FindTaclet taclet = (FindTaclet) TacletForTests
                .getTaclet("TestMatchTaclet_eliminate_variable_declaration").taclet();
        MatchConditions mc =
            (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS, services));

        assertNull(mc,
            "The reason for this bug was related to the introduction of "
                + "statementlist schemavariables and that we could not end the "
                + "match if the size of nonterminalelements was unequal "
                + "The solution was to weaken the check for statement blocks but NOT "
                + "for other statement or expressions containers. The bug occured because "
                + "the weaker test was also " + "performed for expressions.");

        match = TacletForTests.parseTerm("\\<{ {{throw null;} int i = 0;} }\\>true ");
        taclet = (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_throw_in_block").taclet();
        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));
        assertNull(mc, "No match expected.");

        match = TacletForTests.parseTerm("\\<{{ int l1=1;} if (true);}\\>true");
        taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_elim_double_block").taclet();
        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));
        assertNull(mc, "Removed bug #118. No match expected.");

        match = TacletForTests.parseTerm("\\<{ {} {int i;} }\\> true");
        taclet = (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_wrap_blocks").taclet();
        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));
        assertNotNull(mc, "Bug originally failed to match the first empty block.");

        match = TacletForTests.parseTerm("\\<{ {} {int i;} }\\> true");
        taclet = (FindTaclet) TacletForTests
                .getTaclet("TestMatchTaclet_wrap_blocks_two_empty_lists").taclet();
        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));
        assertNotNull(mc, "Bug originally failed to match the first empty block,"
            + " because of he was not able to match two succeeding empty lists.");

        match = TacletForTests.parseTerm("\\<{ {{}} {} }\\> true");
        taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_remove_empty_blocks").taclet();
        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));
        assertNotNull(mc, "Bug matching empty blocks using list svs.");

        match = TacletForTests.parseTerm("\\<{ { int i; } {} }\\> true");
        taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_bug_matching_lists").taclet();
        mc = (taclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));
        assertNotNull(mc, "List matching bug.");

    }

    @Test
    public void testInsequentStateRestriction() {
        FindTaclet restrictedTaclet =
            (FindTaclet) TacletForTests.getTaclet("testInsequentState").taclet();
        FindTaclet unrestrictedTaclet =
            (FindTaclet) TacletForTests.getTaclet("testInsequentState_2").taclet();

        Term match = TacletForTests.parseTerm("{ i := 0 } (i = 0)");
        MatchConditions mc = (restrictedTaclet.getMatcher().matchFind(match,
            MatchConditions.EMPTY_MATCHCONDITIONS, services));
        assertNull(mc, "Test inSequentState failed: matched on term with update prefix");

        mc = (unrestrictedTaclet.getMatcher().matchFind(match,
            MatchConditions.EMPTY_MATCHCONDITIONS, services));
        assertNotNull(mc, "Test inSequentState failed: did not match on term with update prefix");

        match = TacletForTests.parseTerm("i = 0");
        mc = (restrictedTaclet.getMatcher().matchFind(match, MatchConditions.EMPTY_MATCHCONDITIONS,
            services));
        assertNotNull(mc,
            "Test inSequentState failed: did not match on term with without update prefix");

        mc = (unrestrictedTaclet.getMatcher().matchFind(match,
            MatchConditions.EMPTY_MATCHCONDITIONS, services));
        assertNotNull(mc,
            "Test inSequentState failed: did not match on term with without update prefix");
    }


}
