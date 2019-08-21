package org.key_project.exploration;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.antlr.runtime.RecognitionException;
import org.junit.After;
import org.junit.Before;

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

    @After
    public void tearDown(){
        env = null;
        expService = null;
        location = null;
        currentProof = null;
    }

    @org.junit.Test
    public void testAddition() {



//        expService.soundAddition(currentProof.getGoal(currentProof.root()))
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
