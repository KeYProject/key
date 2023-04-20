package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.tacletbuilder.branchlabel.BranchNamingFunctions;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
class BranchNamingFunctionsTest {

    @ParameterizedTest
    @CsvSource(delimiter = '!', value = {
        "\\test![\\test]",
        "\\test(a)![\\test|a]",
        "\\test(a,b)![\\test|a|b]",
        "\\test(    a, b  )![\\test|a|b]",
        "\\test(    a, b  )XX\\test(a) test: \\test(a,b,c,d)end![\\test|a|b]XX[\\test|a] test: [\\test|a|b|c|d]end" })
    void parseNamingFunctionsNames(String input, String exp) {
        assertEquals(exp, parseAndEval(input));
    }

    private String parseAndEval(String label) {
        Services services = new Services(JavaProfile.getDefaultProfile());
        var fn = BranchNamingFunctions.find(label);
        return fn.getName(null, null, null, null);
    }
}
