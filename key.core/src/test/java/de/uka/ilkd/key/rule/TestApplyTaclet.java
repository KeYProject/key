/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.rulefilter.IHTacletFilter;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


/**
 * class tests the apply methods in Taclet
 */
public class TestApplyTaclet {

    final static String[] strs = { "", "(A -> B) -> (!(!(A -> B)))", "", "\\forall s z; p(z)",
        "(A -> B) -> (!(!(A -> B)))", "(A -> B) -> (!(!(A -> B)))", "(A -> B) -> (!(!(A -> B)))",
        "", "",
        "\\<{try{while (1==1) {if (1==2) {break;}} return 1==3; int i=17; } catch (Exception e) { return null;}}\\>A",
        "A & B", "", "", // "s{}::isEmpty(sset)",
        "", // "s{}::size(sset)=0",
        "A & (A & B)", "", "f(const)=const", "const=f(f(const))", "f(const)=const",
        "const=f(const)", "f(const)=const", "A & {i:=0}(const=f(const))", "f(const)=const",
        "A & {i:=0}(const=f(f(const)))", "{i:=0}(f(const)=const)",
        "{i:=1}(const=f(const)) & \\<{i=2;}\\>(const=f(const)) " + "& {i:=0}(const=f(const))",
        "{i:=0}(f(const)=const)",
        "{i:=1}(const=f(const)) & \\<{i=2;}\\>(const=f(const)) " + "& {i:=0}(const=const)", "",
        "\\<{ {} {break;} }\\> true", "", "\\<{ {{}} {{break;}} }\\> true", "",
        "\\<{ try {} catch ( Exception e ) {} catch ( Throwable e ) {} }\\> true", "",
        "\\<{ try {} catch ( Exception e ) {} try {} catch ( Throwable e ) {} }\\> true", "",
        "\\<{ try {} catch ( Exception e ) {break;} catch ( Throwable e ) {continue;} }\\> true",
        "",
        "\\<{ try {} catch ( Exception e ) {break;} try {} catch ( Throwable e ) {continue;} }\\> true",
        "", "\\<{ try {} catch ( Exception e ) {} catch ( Throwable e ) {} finally {} }\\> true",
        "",
        "\\<{ try {} catch ( Exception e ) {} finally {} try {} catch ( Throwable e ) {} }\\> true",
        "",
        "\\<{try{while (1==1) {if (1==2) {break;}} return 1==3; int i=17; } catch (Exception e) { return null;}}\\>\\forall int i; i>0",
        "",
        "\\<{try{ {} while (1==1) {if (1==2) {break;}} return 1==3; int i=17; } catch (Exception e) { return null;}}\\>\\forall int i; i>0",
        "", "A", "A", "", "", "B | A", "B & A", "" };
    Proof[] proof;


    private static Semisequent parseTermForSemisequent(String t) {
        if ("".equals(t)) {
            return Semisequent.EMPTY_SEMISEQUENT;
        }
        SequentFormula cf0 = new SequentFormula(TacletForTests.parseTerm(t));
        return Semisequent.EMPTY_SEMISEQUENT.insert(0, cf0).semisequent();
    }

    @BeforeEach
    public void setUp() {


        TacletForTests.setStandardFile(TacletForTests.testRules);
        TacletForTests.parse();
        assert TacletForTests.services().getNamespaces().programVariables()
                .lookup(new Name("i")) != null;

        proof = new Proof[strs.length / 2];

        for (int i = 0; i < proof.length; i++) {
            Semisequent antec = parseTermForSemisequent(strs[2 * i]);
            Semisequent succ = parseTermForSemisequent(strs[2 * i + 1]);
            Sequent s = Sequent.createSequent(antec, succ);
            proof[i] = new Proof("TestApplyTaclet", TacletForTests.initConfig());
            proof[i].setRoot(new Node(proof[i], s));
        }
    }

    @AfterEach
    public void tearDown() {
        proof = null;
    }


    @Test
    public void testSuccTacletWithoutIf() {
        Term fma = proof[0].root().sequent().succedent().getFirst().formula();
        NoPosTacletApp impright = TacletForTests.getRules().lookup("imp_right");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(impright);
        Goal goal = createGoal(proof[0].root(), tacletIndex);
        PosInOccurrence applyPos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, applyPos, null);
        assertEquals(1, rApplist.size(), "Too many or zero rule applications.");
        RuleApp rApp = rApplist.head();
        assertTrue(rApp.complete(), "Rule App should be complete");
        ImmutableList<Goal> goals = rApp.execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Too many or zero goals for imp-right.");
        Sequent seq = goals.head().sequent();
        assertEquals(seq.antecedent().getFirst().formula(), fma.sub(0),
            "Wrong antecedent after imp-right");
        assertEquals(seq.succedent().getFirst().formula(), fma.sub(1),
            "Wrong succedent after imp-right");
    }


    @Test
    public void testAddingRule() {
        Term fma = proof[0].root().sequent().succedent().getFirst().formula();
        NoPosTacletApp imprightadd =
            TacletForTests.getRules().lookup("TestApplyTaclet_imp_right_add");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(imprightadd);
        Goal goal = createGoal(proof[0].root(), tacletIndex);
        PosInOccurrence applyPos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, applyPos, null);
        assertEquals(1, rApplist.size(), "Too many or zero rule applications.");
        RuleApp rApp = rApplist.head();
        assertTrue(rApp.complete(), "Rule App should be complete");
        ImmutableList<Goal> goals = rApp.execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Too many or zero goals for imp_right_add.");
        Sequent seq = goals.head().sequent();
        assertEquals(seq.antecedent().getFirst().formula(), fma.sub(0),
            "Wrong antecedent after imp_right_add");
        assertEquals(seq.succedent().getFirst().formula(), fma.sub(1),
            "Wrong succedent after imp_right_add");
        ImmutableList<NoPosTacletApp> nfapp = goals.head().indexOfTaclets()
                .getNoFindTaclet(new IHTacletFilter(true, ImmutableSLList.nil()), null);
        Term aimpb = TacletForTests.parseTerm("A -> B");
        assertEquals(1, nfapp.size(), "Cut Rule should be inserted to TacletIndex.");
        assertEquals(
            nfapp.head().instantiations()
                    .getInstantiation(TacletForTests.getSchemaVariables().lookup(new Name("b"))),
            aimpb, "Inserted cut rule's b should be instantiated to A -> B.");
        assertTrue(rApp.complete(), "Rule App should be complete");
        goals = nfapp.head().execute(goals.head(), TacletForTests.services());
        Sequent seq1 = goals.head().sequent();
        Sequent seq2 = goals.tail().head().sequent();
        assertEquals(2, goals.size(), "Preinstantiated cut-rule should be executed");
        assertTrue(
            seq1.succedent().getFirst().formula().equals(aimpb)
                    || seq2.succedent().getFirst().formula().equals(aimpb)
                    || (seq1.succedent().get(1) != null
                            && seq1.succedent().get(1).formula().equals(aimpb))
                    || (seq2.succedent().get(1) != null
                            && seq2.succedent().get(1).formula().equals(aimpb)),
            "A->B should be in the succedent of one of the new goals now, "
                + "it's in the antecedent, anyway.");
    }


    @Test
    public void testSuccTacletAllRight() {
        NoPosTacletApp allright = TacletForTests.getRules().lookup("all_right");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(allright);
        Goal goal = createGoal(proof[1].root(), tacletIndex);
        PosInOccurrence applyPos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, applyPos, null);
        assertEquals(1, rApplist.size(), "Too many or zero rule applications.");
        TacletApp rApp = rApplist.head();
        rApp = rApp.tryToInstantiate(TacletForTests.services());
        assertTrue(rApp.complete(), "Rule App should be complete");
        ImmutableList<Goal> goals = rApp.execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Too many or zero goals for all-right.");
        Sequent seq = goals.head().sequent();
        assertEquals(seq.antecedent(), Semisequent.EMPTY_SEMISEQUENT,
            "Wrong antecedent after all-right");
        assertEquals(seq.succedent().getFirst().formula().op(),
            TacletForTests.getFunctions().lookup(new Name("p")),
            "Wrong succedent after all-right (op mismatch)");
    }

    @Test
    public void testTacletWithIf() {
        NoPosTacletApp close = TacletForTests.getRules().lookup("close_goal");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(close);
        Goal goal = createGoal(proof[2].root(), tacletIndex);
        PosInOccurrence applyPos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, applyPos, null);
        assertEquals(1, rApplist.size(),
            "Too many or zero rule applications.\napp list:" + rApplist);

        TacletApp rApp = rApplist.head();
        ImmutableList<TacletApp> appList =
            rApp.findIfFormulaInstantiations(goal.sequent(), TacletForTests.services());
        assertFalse(appList.isEmpty(), "Match Failed.");
        assertEquals(1, appList.size(), "Too many matches.");
        assertSame(appList.head().instantiations(), rApp.instantiations(), "Wrong match found.");
        assertTrue(appList.head().complete(), "Rule App should be complete");
        ImmutableList<Goal> goals = appList.head().execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Wrong number of goals for close.");
        proof[2].closeGoal(goals.head());
        assertTrue(proof[2].closed(), "Proof should be closed.");
        /*
         * IList<SVInstantiations> svilist=rApp.taclet().matchIf(goal.sequent(),
         * rApp.instantiations(), null); assertTrue("Match Failed.", !svilist.isEmpty());
         * assertTrue("Too many matches.", svilist.size()==1); assertTrue("Wrong match found.",
         * svilist.head()==rApp.instantiations()); assertTrue("Rule App should be complete",
         * rApp.complete()); IList<Goal> goals=rApp.execute(goal, TacletForTests.services());
         * assertTrue("Too many goals for close.", goals.size()==0);
         */
    }


    @Test
    public void testAntecTacletWithoutIf() {
        Term fma = proof[3].root().sequent().antecedent().getFirst().formula();
        NoPosTacletApp impleft = TacletForTests.getRules().lookup("imp_left");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(impleft);
        Goal goal = createGoal(proof[3].root(), tacletIndex);
        PosInOccurrence applyPos = new PosInOccurrence(goal.sequent().antecedent().getFirst(),
            PosInTerm.getTopLevel(), true);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, applyPos, null);
        assertEquals(1, rApplist.size(), "Too many or zero rule applications.");
        RuleApp rApp = rApplist.head();
        assertTrue(rApp.complete(), "Rule App should be complete");
        ImmutableList<Goal> goals = rApp.execute(goal, TacletForTests.services());
        assertEquals(2, goals.size(), "Too many or zero goals for imp-left.");
        Sequent seq = goals.head().sequent();
        if (!seq.succedent().isEmpty()) {
            assertEquals(seq.succedent().getFirst().formula(), fma.sub(0),
                "Wrong succedent after imp-left");
            goals = goals.tail();
            seq = goals.head().node().sequent();
            assertEquals(seq.antecedent().getFirst().formula(), fma.sub(1),
                "Wrong antecedent after imp-left");
        } else {
            assertEquals(seq.antecedent().getFirst().formula(), fma.sub(1),
                "Wrong antecedent after imp-left");
            goals = goals.tail();
            seq = goals.head().node().sequent();

            assertEquals(seq.succedent().getFirst().formula(), fma.sub(0),
                "Wrong succedent after imp-left");
        }
    }


    @Test
    public void testRewriteTacletWithoutIf() {
        NoPosTacletApp contradiction =
            TacletForTests.getRules().lookup("TestApplyTaclet_contradiction");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(contradiction);
        Goal goal = createGoal(proof[0].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel().down(1).down(0).down(0), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Too many or zero rule applications.");
        RuleApp rApp = rApplist.head();
        assertTrue(rApp.complete(), "Rule App should be complete");
        ImmutableList<Goal> goals = rApp.execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Too many or zero goals for contradiction.");
        Sequent seq = goals.head().sequent();
        Term term = seq.succedent().getFirst().formula().sub(1).sub(0).sub(0);
        assertEquals(term, TacletForTests.parseTerm("!B -> !A"));
    }


    @Test
    public void testNoFindTacletWithoutIf() {
        NoPosTacletApp cut = TacletForTests.getRules().lookup("TestApplyTaclet_cut");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        Term t_c = TacletForTests.parseTerm("D");
        tacletIndex.add(cut);
        Goal goal = createGoal(proof[0].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pos, null);
        assertEquals(1, rApplist.size(), "Too many or zero rule applications.");
        TacletApp rApp = rApplist.head().addInstantiation(
            TacletForTests.getSchemaVariables().lookup(new Name("b")), t_c, false,
            proof[0].getServices());
        assertTrue(rApp.complete(), "Rule App should be complete");
        ImmutableList<Goal> goals = rApp.execute(goal, TacletForTests.services());
        assertEquals(2, goals.size(), "Too many or too few goals.");
        Sequent seq1 = goals.head().sequent();
        goals = goals.tail();
        Sequent seq2 = goals.head().sequent();
        if (!seq1.antecedent().isEmpty() && seq1.antecedent().getFirst().formula().equals(t_c)) {
            assertTrue(
                seq2.succedent().getFirst().formula().equals(t_c)
                        || seq2.succedent().get(1).formula().equals(t_c),
                "D is in antecedent of 1st goal but not in succedent of 2nd");
        } else {
            assertTrue(
                seq1.succedent().getFirst().formula().equals(t_c)
                        || seq1.succedent().get(1).formula().equals(t_c),
                "D is not in antecedent and not in succedent " + "of first new goal");
            assertEquals(seq2.antecedent().getFirst().formula(), t_c,
                "D is in succedent of first new goal, but not in antecedent "
                    + "of second new goal");
        }
    }



    /*
     * public String automaticProof(Sequent initSeq, TacletIndex index){ String out=""; Proof
     * proof=new Proof(); proof.setRoot(new Node(proof, initSeq)); IList<Goal>
     * goals=ImmSLList.<Goal>nil(); Goal goal=new Goal(proof.root(),new RuleAppIndex(index));
     * goals=goals.prepend(goal); while (goals.size()!=0) { SequentFormula cfma=null; SequentFormula
     * userCfma=null; // in the real system the //user would select this IList<TacletApp>
     * rapplist=ImmSLList.<TacletApp>nil(); out="\n"+out+("Goals: "+goals+"\n"); goal=goals.head();
     * Iterator<SequentFormula> it=goal.node().sequent().antecedent().iterator(); while
     * (it.hasNext()) { userCfma=it.next(); rapplist=rapplist.prepend(goal.ruleAppIndex().
     * getTacletAppAtAndBelow(TacletFilter.TRUE, new PosInOccurrence(userCfma, PosInTerm.TOP_LEVEL,
     * goal.node().sequent()))); } if (rapplist.isEmpty()) {
     * it=goal.node().sequent().succedent().iterator(); while (it.hasNext()) { userCfma=it.next();
     * rapplist=rapplist.prepend(goal.ruleAppIndex() .getTacletAppAtAndBelow(TacletFilter.TRUE, new
     * PosInOccurrence(userCfma, PosInTerm.TOP_LEVEL, goal.node().sequent()))) ; } }
     * out="\n"+out+("GOAL INDEX:"+goal.indexOfTaclets()); out="\n"+out+("Rule apps: "+rapplist);
     * out="\n"+out+("Choose for if-test: "+rapplist.head()+"\n"); goals=goals.tail(); boolean
     * executed=false; while (!executed && !rapplist.isEmpty()) { IList<ImmMap<SchemaVariable,Term>>
     * mrlist=((Taclet)(rapplist.head().rule())).matchIf(goal.node().sequent(),
     * rapplist.head().instantiations()); out="\n"+out+("List of if-seq matches:"+mrlist); if
     * (!mrlist.isEmpty()) { out+="Execute: "+rapplist.head()+"\n";
     * goals=goals.prepend(rapplist.head().execute(goal)); executed=true; }
     * rapplist=rapplist.tail(); } out="\n"+out+("Tree: "+proof.root()+"\n *** \n"); if (!executed)
     * { return out+"\nPROOF FAILED."; } } if (goals.size()==0) out=out+"\nPROOF."; return out; }
     *
     *
     * public void testNatAutomatically() { TacletAppIndex index=new TacletAppIndex(new
     * TacletIndex()); index.addTaclet(TacletForTests.getRules().lookup("close_goal"));
     * index.addTaclet(TacletForTests.getRules().lookup("imp_left"));
     * index.addTaclet(TacletForTests.getRules().lookup("imp_right"));
     * index.addTaclet(TacletForTests.getRules().lookup("not_left"));
     * index.addTaclet(TacletForTests.getRules().lookup("not_right"));
     * index.addTaclet(TacletForTests.getRules().lookup ("TestApplyTaclet_predsuccelim"));
     * index.addTaclet(pluszeroelim); index.addTaclet(zeropluselim); index.addTaclet(succelim);
     * index.addTaclet(switchsecondsucc); index.addTaclet(switchfirstsucc);
     * index.addTaclet(closewitheq); String s=(automaticProof(seq_testNat, index));
     * assertTrue("Automatic proof with nats failed", s.substring(s.length()-6).equals("PROOF.")); }
     *
     */

    @Test
    public void testIncompleteNoFindTacletApp() {
        NoPosTacletApp cut = TacletForTests.getRules().lookup("TestApplyTaclet_cut");
        assertFalse(cut.complete(), "TacletApp should not be complete, as b is not instantiated");
        SchemaVariable b = TacletForTests.getSchemaVariables().lookup(new Name("b"));
        assertTrue(cut.uninstantiatedVars().contains(b),
            "b should be in the set of not instantiated SVs");
    }

    @Test
    public void testIncompleteSuccTacletApp() {
        TacletApp orright = TacletForTests.getRules().lookup("or_right");
        assertFalse(orright.complete(),
            "TacletApp should not be complete, as SVs are not instantiated");

        Services services = TacletForTests.services();
        SchemaVariable b = TacletForTests.getSchemaVariables().lookup(new Name("b"));
        SchemaVariable c = TacletForTests.getSchemaVariables().lookup(new Name("c"));
        assertEquals(orright.uninstantiatedVars(),
            DefaultImmutableSet.<SchemaVariable>nil().add(b).add(c),
            "b and c should be in the set of not instantiated SVs");
        orright = orright.addInstantiation(b, TacletForTests.parseTerm("A"), false, services);
        assertFalse(orright.complete(),
            "TacletApp should not be complete, as B is not instantiated");
        orright = orright.addInstantiation(c, TacletForTests.parseTerm("B"), false, services);
        assertFalse(orright.complete(), "TacletApp should not be complete, as Position unknown");
        Sequent seq = proof[0].root().sequent();
        orright = orright.setPosInOccurrence(
            new PosInOccurrence(seq.succedent().get(0), PosInTerm.getTopLevel(), false), services);
        assertTrue(orright.complete(),
            "TacletApp should now be complete with Position set and SVs " + "instantiated");
    }


    @Test
    public void testPrgTacletApp() {
        NoPosTacletApp wh0 = TacletForTests.getRules().lookup("TestApplyTaclet_while0");
        SchemaVariable e2 = TacletForTests.getSchemaVariables().lookup(new Name("#e2"));
        SchemaVariable p1 = TacletForTests.getSchemaVariables().lookup(new Name("#p1"));
        // wh0=wh0.addInstantiation(e2,TacletForTests.parseExpr("boolean", "false"));
        // wh0=wh0.addInstantiation(p1,TacletForTests.parsePrg("{if (false){}}"));
        Sequent seq = proof[4].root().sequent();
        PosInOccurrence pio =
            new PosInOccurrence(seq.succedent().get(0), PosInTerm.getTopLevel(), false);
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(wh0);
        Goal goal = createGoal(proof[4].root(), tacletIndex);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pio, null);

        final TacletApp app = rApplist.head();
        assertTrue(app.instantiations().isInstantiated(e2), "#e2 not instantiated");
        assertTrue(app.instantiations().isInstantiated(p1), "#p1 not instantiated");

        ImmutableList<Goal> goals = app.execute(goal, TacletForTests.services);

        assertEquals(1, goals.size(), "Unexpected number of goals");
    }


    @Test
    public void testBugBrokenApply() {
        // several times the following bug got broken
        // The application of
        // 'find (b==>) replacewith(b==>); add (==>b);'
        // resulted in
        // ==> , b==>b instead of
        // b==> , b==>b
        NoPosTacletApp cdr = TacletForTests.getRules().lookup("TestApplyTaclet_cut_direct_r");

        Sequent seq = proof[1].root().sequent();
        PosInOccurrence pio =
            new PosInOccurrence(seq.succedent().get(0), PosInTerm.getTopLevel(), false);
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(cdr);
        Goal goal = createGoal(proof[1].root(), tacletIndex);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pio, null);
        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services);

        assertEquals(2, goals.size(), "Expected two goals");
        assertTrue(
            goals.head().sequent().antecedent().size() == 1
                    && goals.head().sequent().antecedent().iterator().next().formula()
                            .op() == Quantifier.ALL
                    && goals.head().sequent().succedent().size() == 1
                    && goals.head().sequent().succedent().iterator().next().formula()
                            .op() == Quantifier.ALL,
            "First goal should be 'b==>b', but is " + goals.head().sequent());
        goals = goals.tail();
        assertTrue(
            goals.head().sequent().antecedent().size() == 0
                    && goals.head().sequent().succedent().size() == 1
                    && goals.head().sequent().succedent().iterator().next().formula()
                            .op() == Quantifier.ALL,
            "Second goal should be '==>b', but is " + goals.head().sequent());

    }

    @Test
    public void testBugID176() {
        // the last time the bug above had been fixed, the hidden
        // taclets got broken (did not hide anymore)
        // also known as bug #176
        NoPosTacletApp hide_r = TacletForTests.getRules().lookup("TestApplyTaclet_hide_r");

        Sequent seq = proof[1].root().sequent();
        PosInOccurrence pio =
            new PosInOccurrence(seq.succedent().get(0), PosInTerm.getTopLevel(), false);
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(hide_r);
        Goal goal = createGoal(proof[1].root(), tacletIndex);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pio, null);
        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(1, goals.size(), "Expected one goal");
        assertTrue(goals.head().sequent().isEmpty(),
            "Expected '==>', but is " + goals.head().sequent());

    }

    @Test
    public void testBugID177() {
        // bug #177
        NoPosTacletApp al = TacletForTests.getRules().lookup("and_left");

        Sequent seq = proof[5].root().sequent();
        PosInOccurrence pio =
            new PosInOccurrence(seq.antecedent().get(0), PosInTerm.getTopLevel(), true);
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(al);
        Goal goal = createGoal(proof[5].root(), tacletIndex);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pio, null);
        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());


        assertEquals(1, goals.size(), "Expected one goal");
        Iterator<SequentFormula> it = goals.head().sequent().antecedent().iterator();
        assertTrue(
            goals.head().sequent().antecedent().size() == 2
                    && it.next().formula().equals(TacletForTests.parseTerm("A"))
                    && it.next().formula().equals(TacletForTests.parseTerm("B")),
            "Expected 'A, B ==>', but is " + goals.head().sequent());
    }

    @Test
    public void testBugID188() {
        // bug #188

        NoPosTacletApp al = TacletForTests.getRules().lookup("and_left");
        Sequent seq = proof[7].root().sequent();
        PosInOccurrence pio =
            new PosInOccurrence(seq.antecedent().get(0), PosInTerm.getTopLevel(), true);

        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(al);

        Goal goal = createGoal(proof[7].root(), tacletIndex);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pio, null);
        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());


        seq = goals.head().sequent();
        pio = new PosInOccurrence(seq.antecedent().get(1), PosInTerm.getTopLevel(), true);
        tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(al);

        goal = createGoal(goals.head().node(), tacletIndex);

        rApplist = goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pio, null);

        goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(1, goals.size(), "Expected one goal");

        Iterator<SequentFormula> it = goals.head().sequent().antecedent().iterator();

        assertTrue(
            goals.head().sequent().antecedent().size() == 2
                    && goals.head().sequent().succedent().size() == 0
                    && it.next().formula().equals(TacletForTests.parseTerm("A"))
                    && it.next().formula().equals(TacletForTests.parseTerm("B")),
            "Expected 'A, B ==>', but is " + goals.head().sequent());
    }


    @Test
    public void testModalityLevel0() {
        Services services = TacletForTests.services();
        NoPosTacletApp apply_eq_nonrigid = TacletForTests.getRules().lookup("apply_eq_nonrigid");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(apply_eq_nonrigid);
        Goal goal = createGoal(proof[8].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, services);

        assertEquals(4, rApplist.size(), "Expected four rule applications.");

        ImmutableList<TacletApp> appList = ImmutableSLList.nil();
        for (TacletApp aRApplist : rApplist) {
            appList =
                appList.prepend(aRApplist.findIfFormulaInstantiations(goal.sequent(), services));
        }

        assertEquals(1, appList.size(), "Expected one match.");
        assertTrue(appList.head().complete(), "Rule App should be complete");

        ImmutableList<Goal> goals = appList.head().execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Too many or zero goals.");
        Sequent seq = goals.head().sequent();
        Sequent correctSeq = proof[9].root().sequent();
        assertEquals(seq, correctSeq, "Wrong result");
    }


    @Test
    public void testModalityLevel1() {
        Services services = TacletForTests.services();
        NoPosTacletApp apply_eq_nonrigid = TacletForTests.getRules().lookup("apply_eq_nonrigid");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(apply_eq_nonrigid);
        Goal goal = createGoal(proof[10].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, services);

        assertEquals(3, rApplist.size(), "Expected three rule applications.");

        ImmutableList<TacletApp> appList = ImmutableSLList.nil();
        Iterator<TacletApp> appIt = rApplist.iterator();
        while (appIt.hasNext()) {
            appList =
                appList.prepend(appIt.next().findIfFormulaInstantiations(goal.sequent(), services));
        }

        assertEquals(0, appList.size(), "Did not expect a match.");

        Term ifterm = TacletForTests.parseTerm("{i:=0}(f(const)=f(f(const)))");
        SequentFormula ifformula = new SequentFormula(ifterm);
        ImmutableList<IfFormulaInstantiation> ifInsts = ImmutableSLList
                .<IfFormulaInstantiation>nil().prepend(new IfFormulaInstDirect(ifformula));
        appIt = rApplist.iterator();
        while (appIt.hasNext()) {
            TacletApp a =
                appIt.next().setIfFormulaInstantiations(ifInsts, TacletForTests.services());
            if (a != null) {
                appList = appList.prepend(a);
            }
        }

        assertEquals(1, appList.size(), "Expected one match.");
        assertTrue(appList.head().complete(), "Rule App should be complete");

        ImmutableList<Goal> goals = appList.head().execute(goal, TacletForTests.services());
        assertEquals(2, goals.size(), "Expected two goals.");

        { // Goal one
            Sequent correctSeq =
                proof[11].root().sequent().addFormula(ifformula, true, true).sequent();
            assertEquals(goals.head().sequent(), correctSeq, "Wrong result");
        }

        { // Goal two
            Sequent correctSeq =
                proof[10].root().sequent().addFormula(ifformula, false, true).sequent();
            assertEquals(goals.tail().head().sequent(), correctSeq, "Wrong result");
        }
    }


    @Test
    public void testModalityLevel2() {
        Services services = TacletForTests.services();
        NoPosTacletApp make_insert_eq_nonrigid =
            TacletForTests.getRules().lookup("make_insert_eq_nonrigid");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(make_insert_eq_nonrigid);
        Goal goal = createGoal(proof[12].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().antecedent().getFirst(),
            PosInTerm.getTopLevel(), true);
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, services);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Expected one goal.");

        goal = goals.head();

        pos = new PosInOccurrence(goal.sequent().succedent().getFirst(), PosInTerm.getTopLevel(),
            false);
        rApplist = goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, services);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        goals = rApplist.head().execute(goal, TacletForTests.services());
        assertEquals(1, goals.size(), "Expected one goal.");

        Sequent seq = goals.head().sequent();
        Sequent correctSeq = proof[13].root().sequent();
        assertEquals(seq, correctSeq, "Wrong result");
    }


    @Test
    public void testBugEmptyBlock() {
        NoPosTacletApp testApplyTaclet_wrap_blocks_two_empty_lists =
            TacletForTests.getRules().lookup("TestApplyTaclet_wrap_blocks_two_empty_lists");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(testApplyTaclet_wrap_blocks_two_empty_lists);
        Goal goal = createGoal(proof[14].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        // the bug was: the next method throws the exception
        // java.util.NoSuchElementException
        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(1, goals.size(), "Expected one goal.");

        Sequent correctSeq = proof[15].root().sequent();
        assertEquals(correctSeq, goals.head().sequent(), "Wrong result");
    }

    @Test
    public void testCatchList() {
        doTestCatchList(16);
        doTestCatchList(18);
        doTestCatchList(20);
    }


    private void doTestCatchList(int p_proof) {
        NoPosTacletApp test_catch_list0 = TacletForTests.getRules().lookup("test_catch_list0");
        NoPosTacletApp test_catch_list1 = TacletForTests.getRules().lookup("test_catch_list1");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(test_catch_list0);
        tacletIndex.add(test_catch_list1);
        Goal goal = createGoal(proof[p_proof].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete.");

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(1, goals.size(), "Expected one goal.");

        Sequent correctSeq = proof[p_proof + 1].root().sequent();

        Term resultFormula = goals.head().sequent().getFormulabyNr(1).formula();
        Term correctFormula = correctSeq.getFormulabyNr(1).formula();

        assertTrue(resultFormula.equalsModRenaming(correctFormula),
            "Wrong result. Expected:"
                + ProofSaver.printAnything(correctFormula, TacletForTests.services()) + " But was:"
                + ProofSaver.printAnything(resultFormula, TacletForTests.services()));
    }

    private Goal createGoal(Node n, TacletIndex tacletIndex) {
        final BuiltInRuleAppIndex birIndex = new BuiltInRuleAppIndex(new BuiltInRuleIndex());
        return new Goal(n, tacletIndex, birIndex, n.proof().getServices());
    }

    /**
     * tests if the variable sv collector pays attention to schema variables occuring as part of
     * attributes and/or updates (there was a bug where this has been forgotten, and as a result
     * after applying a method contract schemavariables have been introduces into a goal sequent)
     */
    @Test
    public void testTacletVariableCollector() {
        TacletSchemaVariableCollector coll = new TacletSchemaVariableCollector();
        NoPosTacletApp tacletApp =
            TacletForTests.getRules().lookup("testUninstantiatedSVCollector");
        assertNotNull(tacletApp);
        Taclet t = tacletApp.taclet();
        coll.visit(t, false);
        ImmutableSet<SchemaVariable> collSet = DefaultImmutableSet.nil();
        Iterator<SchemaVariable> it = coll.varIterator();
        while (it.hasNext()) {
            SchemaVariable sv = it.next();
            collSet = collSet.add(sv);
        }

        assertEquals(4, collSet.size(), "Expected four uninstantiated variables in taclet " + t
            + ", but found " + collSet.size());
    }

    /**
     * tests a bug, which caused the first statement in a context block to be discarded in cases
     * where the complete program has been matched by the prefix and suffix of the context block
     * i.e. a rule like <code>
     * \find ( <.. ...>\forall u; post )
     * \replacewith (\forall u;<.. ..>post)
     * </code> applied on <code> < method-frame():{ while (...) {...} } >\forall int i; i>0</code>
     * created the goal <code> \forall int i;< method-frame():{ } >i>0 </code> which is of course
     * incorrect.
     */

    @Test
    public void testCompleteContextAddBug() {
        NoPosTacletApp app =
            TacletForTests.getRules().lookup("TestApplyTaclet_allPullOutBehindDiamond");

        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        Goal goal = createGoal(proof[22].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(1, goals.size(), "Expected one goal.");

        // the content of the diamond must not have changed
        ProgramElement expected =
            proof[22].root().sequent().getFormulabyNr(1).formula().javaBlock().program();
        ProgramElement is =
            goals.head().sequent().getFormulabyNr(1).formula().sub(0).javaBlock().program();
        assertEquals(expected, is, "Context has been thrown away.");

    }

    /**
     *
     */
    @Test
    public void testContextAdding() {
        NoPosTacletApp app = TacletForTests.getRules().lookup("TestApplyTaclet_addEmptyStatement");

        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        Goal goal = createGoal(proof[22].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(1, goals.size(), "Expected one goal.");

        // the content of the diamond must not have changed
        ProgramElement expected =
            TacletForTests.parsePrg("{try{ ; while (1==1) {if (1==2) {break;}} return 1==3; "
                + "int i=17; } catch (Exception e) { return null;}}");

        ProgramElement is =
            goals.head().sequent().getFormulabyNr(1).formula().javaBlock().program();
        // FIXME weigl: This test case is spurious:
        // actual.toString() == expected.toString() but internally there is a difference.
        assertTrue(expected.equalsModRenaming(is, new NameAbstractionTable()),
            "Expected:" + expected + "\n but was:" + is);
    }

    /**
     * this test is different from the other empty block removal test
     */
    @Test
    public void testRemoveEmptyBlock() {
        NoPosTacletApp app = TacletForTests.getRules().lookup("TestApplyTaclet_removeEmptyBlock");

        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        Goal goal = createGoal(proof[23].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(1, goals.size(), "Expected one goal.");

        // the content of the diamond must not have changed
        ProgramElement expected =
            TacletForTests.parsePrg("{try{while (1==1) {if (1==2) {break;}} return 1==3; "
                + "int i=17; } catch (Exception e) { return null;}}");

        ProgramElement is =
            goals.head().sequent().getFormulabyNr(1).formula().javaBlock().program();
        assertTrue(expected.equalsModRenaming(is, new NameAbstractionTable()),
            "Expected:" + expected + "\n but was:" + is);
    }

    @Test
    public void testAddExistingFormulaSucc() {
        NoPosTacletApp app = TacletForTests.getRules().lookup("TestApplyTaclet_cut_direct");

        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        Goal goal = createGoal(proof[24].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(2, goals.size(), "Expected two goals.");

        assertEquals(0, goals.head().sequent().antecedent().size(), "Goal should be: ==> false, A");
        assertEquals(2, goals.head().sequent().succedent().size(), "Goal should be: ==> false, A");
        assertEquals("A", goals.head().sequent().succedent().get(0).toString(),
            "Goal should be: ==> A, false");
        assertEquals("false", goals.head().sequent().succedent().get(1).toString(),
            "Goal should be: ==> A, false");


        assertEquals(1, goals.tail().head().sequent().antecedent().size(),
            "Goal should be: A ==> true");
        assertEquals(1, goals.tail().head().sequent().succedent().size(),
            "Goal should be: A ==> true");
        assertEquals("A", goals.tail().head().sequent().antecedent().getFirst().toString(),
            "Goal should be: A ==> true");
        assertEquals("true", goals.tail().head().sequent().succedent().getFirst().toString(),
            "Goal should be: A ==> true");

    }

    @Test
    public void testAddExistingFormulaAntec() {
        NoPosTacletApp app = TacletForTests.getRules().lookup("TestApplyTaclet_cut_direct");

        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        Goal goal = createGoal(proof[25].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().antecedent().getFirst(),
            PosInTerm.getTopLevel(), true);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(2, goals.size(), "Expected two goals.");

        assertEquals(2, goals.tail().head().sequent().antecedent().size(),
            "Goal should be: true, A ==> ");
        assertEquals(0, goals.tail().head().sequent().succedent().size(),
            "Goal should be: true, A ==> ");
        assertEquals("A", goals.tail().head().sequent().antecedent().get(0).toString(),
            "Goal should be: true, A ==> ");
        assertEquals("true", goals.tail().head().sequent().antecedent().get(1).toString(),
            "Goal should be: true, A ==> ");

        assertEquals(1, goals.head().sequent().antecedent().size(), "Goal should be: false ==> A");
        assertEquals(1, goals.head().sequent().succedent().size(), "Goal should be: false ==> A");
        assertEquals("false", goals.head().sequent().antecedent().get(0).toString(),
            "Goal should be: false ==> A");
        assertEquals("A", goals.head().sequent().succedent().get(0).toString(),
            "Goal should be: false ==> A");
    }
    /*
     * "","A", "A","", "","B,A", "B,A",""
     */

    @Test
    public void testAddExistingFormulaTwoInSucc() {

        // setup
        NoPosTacletApp orRight = TacletForTests.getRules().lookup("or_right");
        NoPosTacletApp app = TacletForTests.getRules().lookup("TestApplyTaclet_cut_direct");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        tacletIndex.add(orRight);

        Goal goal = createGoal(proof[26].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());
        goal = goals.head();

        // end of setup


        pos = new PosInOccurrence(goal.sequent().succedent().getFirst(), PosInTerm.getTopLevel(),
            false);

        rApplist = goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(2, goals.size(), "Expected two goals.");

        assertEquals(0, goals.head().sequent().antecedent().size(),
            "Goal should be: ==> B, false, A");
        assertEquals(3, goals.head().sequent().succedent().size(),
            "Goal should be: ==> B, false, A");
        assertEquals("B", goals.head().sequent().succedent().get(0).toString(),
            "Goal should be:  ==> B, false, A");
        assertEquals("false", goals.head().sequent().succedent().get(1).toString(),
            "Goal should be:  ==> B, false, A");
        assertEquals("A", goals.head().sequent().succedent().get(2).toString(),
            "Goal should be:  ==> B, false, A");


        assertEquals(1, goals.tail().head().sequent().antecedent().size(),
            "Goal should be: B ==> true, A");
        assertEquals(2, goals.tail().head().sequent().succedent().size(),
            "Goal should be: B ==> true, A");
        assertEquals("B", goals.tail().head().sequent().antecedent().get(0).toString(),
            "Goal should be:B  ==> true, A");
        assertEquals("true", goals.tail().head().sequent().succedent().get(0).toString(),
            "Goal should be:B  ==> true, A");
        assertEquals("A", goals.tail().head().sequent().succedent().get(1).toString(),
            "Goal should be:B  ==> true, A");

    }

    @Test
    public void testAddExistingFormulaTwoInSucc2() {

        // setup
        NoPosTacletApp orRight = TacletForTests.getRules().lookup("or_right");
        NoPosTacletApp app = TacletForTests.getRules().lookup("TestApplyTaclet_cut_direct");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        tacletIndex.add(orRight);

        Goal goal = createGoal(proof[26].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());
        goal = goals.head();

        // end of setup


        pos =
            new PosInOccurrence(goal.sequent().succedent().get(1), PosInTerm.getTopLevel(), false);

        rApplist = goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(2, goals.size(), "Expected two goals.");
        assertEquals(0, goals.head().sequent().antecedent().size(),
            "Goal should be: ==> B, A, false");
        assertEquals(3, goals.head().sequent().succedent().size(),
            "Goal should be: ==> B, A, false");
        assertEquals("B", goals.head().sequent().succedent().get(0).toString(),
            "Goal should be:  ==> B, A, false");
        assertEquals("A", goals.head().sequent().succedent().get(1).toString(),
            "Goal should be:  ==> B, A, false");
        assertEquals("false", goals.head().sequent().succedent().get(2).toString(),
            "Goal should be:  ==> B, A, false");


        assertEquals(1, goals.tail().head().sequent().antecedent().size(),
            "Goal should be: A ==> B, true");
        assertEquals(2, goals.tail().head().sequent().succedent().size(),
            "Goal should be: A ==> B, true");
        assertEquals("A", goals.tail().head().sequent().antecedent().get(0).toString(),
            "Goal should be:A ==> B, true");
        assertEquals("B", goals.tail().head().sequent().succedent().get(0).toString(),
            "Goal should be:A ==> B, true");
        assertEquals("true", goals.tail().head().sequent().succedent().get(1).toString(),
            "Goal should be:A ==> B, true");

    }

    @Test
    public void testAddExistingFormulaTwoInAntec() {

        // setup
        NoPosTacletApp andLeft = TacletForTests.getRules().lookup("and_left");
        NoPosTacletApp app = TacletForTests.getRules().lookup("TestApplyTaclet_cut_direct");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        tacletIndex.add(andLeft);

        Goal goal = createGoal(proof[27].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().antecedent().getFirst(),
            PosInTerm.getTopLevel(), true);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());
        goal = goals.head();

        // end of setup


        pos =
            new PosInOccurrence(goal.sequent().antecedent().get(0), PosInTerm.getTopLevel(), true);

        rApplist = goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(2, goals.size(), "Expected two goals.");

        assertEquals(2, goals.head().sequent().antecedent().size(),
            "Goal should be: false, A ==> B ");
        assertEquals(1, goals.head().sequent().succedent().size(),
            "Goal should be: false, A ==> B");
        assertEquals("false", goals.head().sequent().antecedent().get(0).toString(),
            "Goal should be:  false, A ==> B");
        assertEquals("A", goals.head().sequent().antecedent().get(1).toString(),
            "Goal should be:  false, A ==> B");
        assertEquals("B", goals.head().sequent().succedent().get(0).toString(),
            "Goal should be:  false, A ==> B");


        assertEquals(3, goals.tail().head().sequent().antecedent().size(),
            "Goal should be: B, true, A ==>");
        assertEquals(0, goals.tail().head().sequent().succedent().size(),
            "Goal should be:  B, true, A ==>");
        assertEquals("B", goals.tail().head().sequent().antecedent().get(0).toString(),
            "Goal should be: B, true, A ==>");
        assertEquals("true", goals.tail().head().sequent().antecedent().get(1).toString(),
            "Goal should be: B, true, A ==>");
        assertEquals("A", goals.tail().head().sequent().antecedent().get(2).toString(),
            "Goal should be: B, true, A ==>");

    }

    @Test
    public void testAddExistingFormulaTwoInAntec2() {

        // setup
        NoPosTacletApp andLeft = TacletForTests.getRules().lookup("and_left");
        NoPosTacletApp app = TacletForTests.getRules().lookup("TestApplyTaclet_cut_direct");
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(app);
        tacletIndex.add(andLeft);

        Goal goal = createGoal(proof[27].root(), tacletIndex);
        PosInOccurrence pos = new PosInOccurrence(goal.sequent().antecedent().getFirst(),
            PosInTerm.getTopLevel(), true);

        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        ImmutableList<Goal> goals = rApplist.head().execute(goal, TacletForTests.services());
        goal = goals.head();

        // end of setup


        pos =
            new PosInOccurrence(goal.sequent().antecedent().get(1), PosInTerm.getTopLevel(), true);

        rApplist = goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pos, null);

        assertEquals(1, rApplist.size(), "Expected one rule application.");
        assertTrue(rApplist.head().complete(), "Rule App should be complete");

        goals = rApplist.head().execute(goal, TacletForTests.services());

        assertEquals(2, goals.size(), "Expected two goals.");

        assertEquals(2, goals.head().sequent().antecedent().size(),
            "Goal should be: B, false ==> A ");
        assertEquals(1, goals.head().sequent().succedent().size(),
            "Goal should be: B, false  ==> A");
        assertEquals("B", goals.head().sequent().antecedent().get(0).toString(),
            "Goal should be:  B, false  ==> A");
        assertEquals("false", goals.head().sequent().antecedent().get(1).toString(),
            "Goal should be:  B, false  ==> A");
        assertEquals("A", goals.head().sequent().succedent().get(0).toString(),
            "Goal should be:  B, false  ==> A");


        assertEquals(3, goals.tail().head().sequent().antecedent().size(),
            "Goal should be: B, A, true  ==> ");
        assertEquals(0, goals.tail().head().sequent().succedent().size(),
            "Goal should be:   B, A, true  ==> ");
        assertEquals("B", goals.tail().head().sequent().antecedent().get(0).toString(),
            "Goal should be:  B, A, true  ==> ");
        assertEquals("A", goals.tail().head().sequent().antecedent().get(1).toString(),
            "Goal should be:  B, A, true  ==> ");
        assertEquals("true", goals.tail().head().sequent().antecedent().get(2).toString(),
            "Goal should be:  B, A, true  ==> ");

    }


}
