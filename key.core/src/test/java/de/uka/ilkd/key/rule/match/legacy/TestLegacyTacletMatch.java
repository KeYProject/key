/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.legacy;

import java.io.File;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableArray;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;


/**
 * tests if match checks the variable conditions in Taclets.
 */
public class TestLegacyTacletMatch {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestLegacyTacletMatch.class);

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
    public void testStatementListMatch() {
        Term match = TacletForTests.parseTerm("\\<{ l1:{l2:{while (true) {break; "
            + "int k=1; {int j = 1; j++;} int c = 56;}}} }\\> true");

        FindTaclet break_while =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_break_while").taclet();

        MatchConditions svi = new LegacyTacletMatcher(break_while).matchJavaBlock(match,
            break_while.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);

        assertNotNull(svi, "Matches have been expected.");

        SchemaVariable sv = TacletForTests.svLookup("#stmnt_list");
        assertTrue(svi.getInstantiations().isInstantiated(sv),
            "Expected list of statement to be instantiated.");
        assertEquals(3, ((ImmutableArray<?>) svi.getInstantiations().getInstantiation(sv)).size(),
            "The three statements behind the break should be matched.");
    }

    @Test
    public void testProgramMatch0() {
        Term match = TacletForTests
                .parseTerm("\\<{ l1:{l2:{while (true) {break;} " + "int k=1;}} }\\> true");
        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_whileright").taclet();
        MatchConditions svi = new LegacyTacletMatcher(taclet).matchJavaBlock(match, taclet.find(),
            MatchConditions.EMPTY_MATCHCONDITIONS, services);

        assertNotNull(svi, "There should be instantiations");
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#e2")),
            "#e2 should be instantiated");
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#p1")),
            "#p1 should be instantiated");

        Term matchTwo = TacletForTests.parseTerm(
            "\\<{ l1:{l2:{while (true) {boolean b=true; break;} " + "}int k=1;} }\\> true");
        FindTaclet tacletTwo =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_whileright_labeled").taclet();

        svi = new LegacyTacletMatcher(tacletTwo).matchJavaBlock(matchTwo, tacletTwo.find(),
            MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNotNull(svi);

        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#e2")));
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#p1")));
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#lab")));

        Term match3 = TacletForTests.parseTerm(
            "\\<{ l1:{l2:{while (true) {boolean b=false; break;} " + "int k=1;}} }\\> true");
        FindTaclet taclet3 =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_whileright_labeled").taclet();

        svi = new LegacyTacletMatcher(taclet3).matchJavaBlock(match3, taclet3.find(),
            MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNull(svi);

        Term emptyBlock = TacletForTests.parseTerm("\\<{ { {} int i = 0; } }\\> true");
        FindTaclet empty_block_taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_empty_block").taclet();

        svi = new LegacyTacletMatcher(empty_block_taclet).matchJavaBlock(emptyBlock,
            empty_block_taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNotNull(svi);

        Term emptyBlock2 = TacletForTests.parseTerm("\\<{ { {} } }\\> true");

        svi = new LegacyTacletMatcher(empty_block_taclet).matchJavaBlock(emptyBlock2,
            empty_block_taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);

        assertNotNull(svi);

        LOGGER.debug("%%%%%%%%%%%%");
        Term emptyBlock3 = TacletForTests.parseTerm("\\<{ { {} l1:{} } }\\> true");
        svi = new LegacyTacletMatcher(empty_block_taclet).matchJavaBlock(emptyBlock3,
            empty_block_taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNotNull(svi);


        FindTaclet var_decl_taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_variable_declaration").taclet();

        svi = new LegacyTacletMatcher(var_decl_taclet).matchJavaBlock(emptyBlock,
            var_decl_taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNull(svi);

        Term emptyLabel = TacletForTests.parseTerm("\\<{ { l1:{} } }\\> true");
        FindTaclet empty_label_taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_empty_label").taclet();
        svi = new LegacyTacletMatcher(empty_label_taclet).matchJavaBlock(emptyLabel,
            empty_label_taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNotNull(svi);

        Term emptyLabel2 = TacletForTests.parseTerm("\\<{ l2:{ l1:{} } }\\> true");
        svi = new LegacyTacletMatcher(empty_label_taclet).matchJavaBlock(emptyLabel2,
            empty_label_taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNotNull(svi);

        Term emptyLabel3 =
            TacletForTests.parseTerm("\\<{ {l3:{{l2:{l1:{}}}} int i = 0;} }\\> true");
        svi = new LegacyTacletMatcher(empty_label_taclet).matchJavaBlock(emptyLabel3,
            empty_label_taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNotNull(svi);
    }


    @Test
    public void testProgramMatch1() {
        Services services = TacletForTests.services();
        de.uka.ilkd.key.java.Recoder2KeY c2k =
            new de.uka.ilkd.key.java.Recoder2KeY(services, new NamespaceSet());
        JavaBlock jb = c2k.readBlock("{ int i; int j; i=++j;" + " while(true) {break;}}",
            c2k.createEmptyContext());

        de.uka.ilkd.key.java.StatementBlock sb = (de.uka.ilkd.key.java.StatementBlock) jb.program();

        JavaBlock javaBlock = JavaBlock.createJavaBlock(new de.uka.ilkd.key.java.StatementBlock(
            new ImmutableArray<>((de.uka.ilkd.key.java.Statement) sb.getChildAt(2),
                (de.uka.ilkd.key.java.Statement) sb.getChildAt(3))));


        Term match = TB.dia(javaBlock, TB.tt());

        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_preincrement").taclet();

        MatchConditions svi = new LegacyTacletMatcher(taclet).matchJavaBlock(match, taclet.find(),
            MatchConditions.EMPTY_MATCHCONDITIONS, services);


        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#slhs1")));
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#slhs2")));
    }

    @Test
    public void testProgramMatch2() {
        Term match = TacletForTests.parseTerm("\\<{int i; int k;}\\>(\\<{for (int i=0;"
            + " i<2; i++) {break;} " + "int k=1; }\\> true)");
        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestMatchTaclet_for_right").taclet();
        MatchConditions svi = new LegacyTacletMatcher(taclet).matchJavaBlock(match.sub(0),
            taclet.find(), MatchConditions.EMPTY_MATCHCONDITIONS, services);


        assertNotNull(svi);
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#loopInit")));
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#guard")));
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#forupdates")));
        assertTrue(svi.getInstantiations().isInstantiated(TacletForTests.svLookup("#p1")));
    }


}
