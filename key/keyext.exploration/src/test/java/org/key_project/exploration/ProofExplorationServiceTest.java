package org.key_project.exploration;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.junit.*;
import org.key_project.util.collection.ImmutableList;

import java.io.File;
import java.net.URL;

public class ProofExplorationServiceTest {
    ProofExplorationService expService;
    Proof currentProof;
    File location;
    KeYEnvironment<?> env;

    @Before
    public void setup() throws ProblemLoaderException {
        location = new File("src/test/resources//org/key_project/exploration/testAdditions.key");
        Assume.assumeTrue("File testAdditions.key not found.", location.exists());
        env = KeYEnvironment.load(location);
        currentProof = env.getLoadedProof();
        expService = new ProofExplorationService(currentProof, env.getServices());
    }

    //p -> q -> !q -> !p
    @After
    public void tearDown() {
        env = null;
        expService = null;
        location = null;
        currentProof = null;
    }


//region Addition

    /**
     * Tests that the added term is added correctly and that meta data was added as well
     */
    @Test
    public void testAdditionAntec() {
        Term add = parseTerm("p");
        expService.soundAddition(currentProof.getGoal(currentProof.root()), add, true);
        ImmutableList<Goal> goals = currentProof.openGoals();

        Assert.assertEquals("Two new goals created", 2, goals.size());

        Goal first = goals.head();
        Goal second = goals.tail().head();

        ExplorationNodeData lookup = first.node().lookup(ExplorationNodeData.class);
        Assert.assertNotNull("First goal is marked as exploration node", lookup);

        ExplorationNodeData lookup2 = second.node().lookup(ExplorationNodeData.class);
        Assert.assertNotNull("Second goal is marked as exploration node", lookup2);

        Goal withAddedTerm;
        Goal justification;

        if (!first.node().sequent().antecedent().isEmpty()) {
            withAddedTerm = first;
            justification = second;

        } else {
            withAddedTerm = second;
            justification = first;
        }

        testAddition(withAddedTerm, justification, add, true);
        Assert.assertFalse(checkNodeForExplorationDataAndAction(withAddedTerm.node()));
        Assert.assertFalse(checkNodeForExplorationDataAndAction(justification.node()));


        Assert.assertTrue("Parent is marked as ExplorationNode and data contains Exploration Action", checkNodeForExplorationDataAndAction(withAddedTerm.node().parent()));

        Assert.assertFalse(checkNodeForExplorationDataAndAction(withAddedTerm.node()));
        Assert.assertFalse(checkNodeForExplorationDataAndAction(justification.node()));

    }

    /**
     * Test tests that the added term is added correctly and that meta data was added as well
     */
    @Test
    public void testAdditionSucc() {
        Term added = parseTerm("q");
        expService.soundAddition(currentProof.getGoal(currentProof.root()), added, false);
        ImmutableList<Goal> goals = currentProof.openGoals();

        Assert.assertEquals("Two new goals created", 2, goals.size());

        Goal first = goals.head();
        Goal second = goals.tail().head();

        ExplorationNodeData lookup = first.node().lookup(ExplorationNodeData.class);
        Assert.assertNotNull("First goal is marked as exploration node", lookup);

        ExplorationNodeData lookup2 = second.node().lookup(ExplorationNodeData.class);
        Assert.assertNotNull("Second goal is marked as exploration node", lookup2);

        Goal withAddedTerm;
        Goal justification;

        if (!first.node().sequent().antecedent().isEmpty()) {
            withAddedTerm = second;
            justification = first;

        } else {
            withAddedTerm = first;
            justification = second;
        }

        testAddition(withAddedTerm, justification, added, false);

        Assert.assertTrue("Parent is marked as ExplorationNode and data contains Exploration Action",
                checkNodeForExplorationDataAndAction(withAddedTerm.node().parent()));

        Assert.assertFalse(checkNodeForExplorationDataAndAction(withAddedTerm.node()));
        Assert.assertFalse(checkNodeForExplorationDataAndAction(justification.node()));


    }


    //region Change

    /**
     * Test changing the root formula
     */
    @Test
    public void testChangeFormula() {
        Term change = parseTerm("p->p");
        ImmutableList<Goal> goals = currentProof.openGoals();
        Assert.assertSame("Prerequisite for test", 1, goals.size());
        Sequent sequent = goals.head().node().sequent();
        PosInOccurrence pio = new PosInOccurrence(sequent.succedent().get(0), PosInTerm.getTopLevel(), false);
        expService.applyChangeFormula(goals.head(), pio, sequent.succedent().get(0).formula(), change);
        ImmutableList<Goal> newCreatedGoals = currentProof.openGoals();

        Assert.assertEquals("Two new goals created", 2, newCreatedGoals.size());

        //find hide branch
        Goal applicationBranch = newCreatedGoals.head().isAutomatic() ? newCreatedGoals.head() :
                newCreatedGoals.tail().head();
        Goal justificationBranch = !newCreatedGoals.head().isAutomatic() ? newCreatedGoals.head() :
                newCreatedGoals.tail().head();

        //System.out.println("applicationBranch = " + applicationBranch.sequent());
        //System.out.println("justificationBranch.sequent() = " + justificationBranch.sequent());
        //check meta data
        Node hideNode = applicationBranch.node().parent();

        Assert.assertNotNull(hideNode.lookup(ExplorationNodeData.class));
        Assert.assertNotNull(justificationBranch.node().lookup(ExplorationNodeData.class));

        Assert.assertEquals("Hide Right was applied", new Name("hide_right"), hideNode.getAppliedRuleApp().rule().name());
        //set all goals to interactive
        justificationBranch.setEnabled(true);
        //perform proof, it has to close
        env.getProofControl().startAndWaitForAutoMode(currentProof, newCreatedGoals);
        Assert.assertTrue("Proof is closed", currentProof.closed());

    }


    /**
     * Tests that sizes are as expected after addition
     */
    private void testAddition(Goal withAddedTerm, Goal justification, Term added, boolean antec) {
        Semisequent semiSeqAdded = antec ? withAddedTerm.sequent().antecedent() : withAddedTerm.sequent().succedent();
        Semisequent parentSemiSeqOfAdded = antec ? withAddedTerm.node().parent().sequent().antecedent() : withAddedTerm.node().parent().sequent().succedent();

        Semisequent semiSeqUntouched = !antec ? withAddedTerm.sequent().antecedent() : withAddedTerm.sequent().succedent();
        Semisequent parentSemiSeqOfUntouched = !antec ? withAddedTerm.node().parent().sequent().antecedent() : withAddedTerm.node().parent().sequent().succedent();


        Assert.assertSame("The size of the added semisequent has changed", semiSeqAdded.size(), parentSemiSeqOfAdded.size() + 1);
        Assert.assertEquals("Added Term is indeed added", semiSeqAdded.get(0).formula(), added);
        Assert.assertFalse("Justification branch is marked as interactive", justification.isAutomatic());

        Assert.assertSame("The size if untouched semisequents is the same", semiSeqUntouched.size(), parentSemiSeqOfUntouched.size());
        Assert.assertEquals("The  untouched semisequents are equal", semiSeqUntouched, parentSemiSeqOfUntouched);

        Node parent = withAddedTerm.node().parent();

        Assert.assertEquals("Both nodes have the same parent", parent, justification.node().parent());
        Assert.assertEquals("The addition was inserted using the cut rule", new Name("cut"), parent.getAppliedRuleApp().rule().name());


    }

    /**
     * Test that exploration metadata have been set to the node
     */
    private boolean checkNodeForExplorationDataAndAction(Node parent) {
        boolean foundExploration = false;
        boolean foundExplorationAction = false;

        ExplorationNodeData lookup = parent.lookup(ExplorationNodeData.class);
        if (lookup != null) {
            foundExploration = true;
            String explorationAction = lookup.getExplorationAction();
            if (explorationAction != null) {
                foundExplorationAction = true;
            }
        }

        return foundExploration & foundExplorationAction;

    }

    private Term parseTerm(String term) {
        KeyIO io = new KeyIO(env.getServices());
        return io.parseExpression(term);
    }
}
