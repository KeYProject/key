package de.uka.ilkd.key.rule.match.vm;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.HelperClassForTests;

public class VMTacletMatcherTest {

    @Test
    public void matchPropositionalFormula() throws ParserException {
        HelperClassForTests helper = new HelperClassForTests();
        ProofAggregate pa = helper.parse(new File(HelperClassForTests.TESTCASE_DIRECTORY + "/tacletmatch/tacletMatch1.key"));
        Taclet taclet1 = pa.getFirstProof().getInitConfig().lookupActiveTaclet(new Name("taclet_match_rule_1"));
        assertNotNull("Taclet required for test not found", taclet1);
        assertTrue("Taclet should be a FindTaclet, but is not.", taclet1 instanceof FindTaclet);
        
        
        Term findTerm = ((FindTaclet)taclet1).find();
        VMTacletMatcher matcher = new VMTacletMatcher(findTerm);
        
        final Services services = pa.getFirstProof().getServices();
        
        final String[] matchingFormulas = {"A & B", "(!A | (A<->B)) & B",
                "A & (B & A)", "(\\forall int x; x>=0) & A"
        };
         
        for (String fml : matchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);

            MatchConditions mc = matcher.match(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);
        
            assertNotNull("Expected that " + findTerm + " matches " + toMatch + " but did not.", mc);
            assertSame(mc.getInstantiations().lookupValue(new Name("phi")), toMatch.sub(0));
            assertSame(mc.getInstantiations().lookupValue(new Name("psi")), toMatch.sub(1));
        }
        

        final String[] notMatchingFormulas = {"A | (B & A)", "A", 
                "\\forall int x;(x>=0 & A)"
        };
        for (String fml : notMatchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);
            MatchConditions mc = matcher.match(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNull("Expected that " + findTerm + " does not match " + toMatch + " but it did.", mc);
        }
    }
    
    @Test
    public void matchFunctionTerm() throws ParserException {
        HelperClassForTests helper = new HelperClassForTests();
        ProofAggregate pa = helper.parse(new File(HelperClassForTests.TESTCASE_DIRECTORY + "/tacletmatch/tacletMatch1.key"));
        Taclet taclet1 = pa.getFirstProof().getInitConfig().lookupActiveTaclet(new Name("taclet_match_rule_2"));
        assertNotNull("Taclet required for test not found", taclet1);
        assertTrue("Taclet should be a FindTaclet, but is not.", taclet1 instanceof FindTaclet);
        
        
        Term findTerm = ((FindTaclet)taclet1).find();
        VMTacletMatcher matcher = new VMTacletMatcher(findTerm);
        
        final Services services = pa.getFirstProof().getServices();
        
        final String[] matchingFormulas = {"f(1, 1, 2)", "f(c, c, d)"};
         
        for (String fml : matchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);

            MatchConditions mc = matcher.match(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);
        
            assertNotNull("Expected that " + findTerm + " matches " + toMatch + " but did not.", mc);
        }

        final String[] notMatchingFormulas = {"f(1,2,1)", "g(1,1,2)", "g(1,2,1)", 
                "h(1,1)", "h(1,2)", "c", "z(1,1,1,1)", "f(c,d,c)"
        };
        for (String fml : notMatchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);
            MatchConditions mc = matcher.match(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNull("Expected that " + findTerm + " does not match " + toMatch + " but it did.", mc);
        }

        
    }

}
