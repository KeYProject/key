package org.key_project.exploration;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.antlr.runtime.RecognitionException;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.key_project.util.collection.ImmutableList;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.net.URL;

public class ProofExplorationServiceTest {

    ProofExplorationService expService;

    Proof currentProof;

    File location ;

    KeYEnvironment<?> env;

    @Before
    public void setup() throws ProblemLoaderException {
        URL url = getClass().getClassLoader().getResource("org/key_project/exploration/testAdditions.key");
        location = new File(url.getPath());
        env = KeYEnvironment.load(location, null, null, null); // env.getLoadedProof() returns performed proof if a *.proof file is loaded
        currentProof = env.getLoadedProof();
        expService = new ProofExplorationService(currentProof, env.getServices());
    }

    //p -> q -> !q -> !p
    @After
    public void tearDown(){
        env = null;
        expService = null;
        location = null;
        currentProof = null;
    }

    /**
     * Test tests that the added term is added correctly and that meta data was added as well
     * @throws IOException
     * @throws RecognitionException
     */
    @org.junit.Test
    public void testAdditionAntec() throws IOException, RecognitionException {
        Term p = parseTerm("p");
        expService.soundAddition(currentProof.getGoal(currentProof.root()), p, true);
        ImmutableList<Goal> goals = currentProof.openGoals();

        Assert.assertTrue("Two new goals created", goals.size() ==2);

        Goal first = goals.head();
        Goal second = goals.tail().head();

        ExplorationNodeData lookup = first.node().lookup(ExplorationNodeData.class);
        Assert.assertNotNull("First goal is marked as exploration node", lookup);

        ExplorationNodeData lookup2 = second.node().lookup(ExplorationNodeData.class);
        Assert.assertNotNull("Second goal is marked as exploration node", lookup2);

        Goal withAddedTerm = null;
        Goal justification = null;

        if(!first.node().sequent().antecedent().isEmpty()){
           withAddedTerm = first;
           justification = second;

        } else {
            withAddedTerm = second;
            justification = first;
        }

        testAddition(withAddedTerm, justification, p, true);
        Assert.assertFalse(checkNodeForExplorationDataAndAction(withAddedTerm.node()));
        Assert.assertFalse(checkNodeForExplorationDataAndAction(justification.node()));

    }

    /**
     * Test tests that the added term is added correctly and that meta data was added as well
     * @throws IOException
     * @throws RecognitionException
     */
    @org.junit.Test
    public void testAdditionSucc() throws IOException, RecognitionException {
        Term added = parseTerm("q");
        expService.soundAddition(currentProof.getGoal(currentProof.root()), added, false);
        ImmutableList<Goal> goals = currentProof.openGoals();

        Assert.assertTrue("Two new goals created", goals.size() ==2);

        Goal first = goals.head();
        Goal second = goals.tail().head();

        ExplorationNodeData lookup = first.node().lookup(ExplorationNodeData.class);
        Assert.assertNotNull("First goal is marked as exploration node", lookup);

        ExplorationNodeData lookup2 = second.node().lookup(ExplorationNodeData.class);
        Assert.assertNotNull("Second goal is marked as exploration node", lookup2);

        Goal withAddedTerm = null;
        Goal justification = null;

        if(!first.node().sequent().antecedent().isEmpty()){
            withAddedTerm = second;
            justification = first;

        } else {
            withAddedTerm = first;
            justification = second;
        }

        testAddition(withAddedTerm, justification, added, false);
        Assert.assertFalse(checkNodeForExplorationDataAndAction(withAddedTerm.node()));
        Assert.assertFalse(checkNodeForExplorationDataAndAction(justification.node()));

    }

    private void testAddition(Goal withAddedTerm, Goal justification, Term added, boolean antec){
        Semisequent semiSeqAdded =  antec? withAddedTerm.sequent().antecedent() : withAddedTerm.sequent().succedent();
        Semisequent parentSemiSeqOfAdded = antec? withAddedTerm.node().parent().sequent().antecedent(): withAddedTerm.node().parent().sequent().succedent();

        Semisequent semiSeqUntouched =  !antec? withAddedTerm.sequent().antecedent() : withAddedTerm.sequent().succedent();
        Semisequent parentSemiSeqOfUntouched = !antec? withAddedTerm.node().parent().sequent().antecedent(): withAddedTerm.node().parent().sequent().succedent();


        Assert.assertTrue("The size of the added semisequent has changed", semiSeqAdded.size() == parentSemiSeqOfAdded.size() + 1);
        Assert.assertEquals("Added Term is indeed added", semiSeqAdded.get(0).formula(), added);
        Assert.assertFalse("Justification branch is marked as interactive", justification.isAutomatic());

        Assert.assertTrue("The size if untouched semiseuqents is the same", semiSeqUntouched.size() == parentSemiSeqOfUntouched.size());
        Assert.assertEquals("The  untouched semiseuqents are equal", semiSeqUntouched, parentSemiSeqOfUntouched);

        Node parent = withAddedTerm.node().parent();
        Assert.assertEquals("Both nodes have the same parent", parent, justification.node().parent());
        Assert.assertEquals("The addition was inserted using the cut rule", new Name("cut"), parent.getAppliedRuleApp().rule().name());
        Assert.assertTrue("Parent is marked as ExplorationNode and data contains Exploration Action", checkNodeForExplorationDataAndAction(parent));


    }

    private boolean checkNodeForExplorationDataAndAction(Node parent) {
        boolean foundExploration = false;
        boolean foundExplorationAction = false;

        ExplorationNodeData lookup = parent.lookup(ExplorationNodeData.class);
        if(lookup != null){
            foundExploration = true;
            String explorationAction = lookup.getExplorationAction();
            if (explorationAction != null){
                foundExplorationAction = true;
            }
        }

        return foundExploration & foundExplorationAction;

    }

    private Term parseTerm(String term)  throws IOException, RecognitionException{
        StringReader br = null;
        br = new StringReader(term);
        KeYParserF parser = new KeYParserF(ParserMode.TERM, new KeYLexerF(br, ""),
                new Recoder2KeY(env.getServices(), env.getServices().getNamespaces()), env.getServices(),
                env.getServices().getNamespaces(), null);
        Term t = parser.term();
        return t;
    }


}
