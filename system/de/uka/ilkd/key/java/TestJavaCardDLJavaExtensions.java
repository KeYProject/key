package de.uka.ilkd.key.java;

import java.io.File;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.TestCase;

public class TestJavaCardDLJavaExtensions extends TestCase {

    private HelperClassForTests helper = new HelperClassForTests();
    
    public static final String testpath = System.getProperty("key.home")
    + File.separator + "examples"
    + File.separator + "_testcase" + File.separator
    + "javacardDLExtensions" + File.separator;

    
    public TestJavaCardDLJavaExtensions() {
        
    }
    
    public void testTypeNotInScopeShouldNotBeFound() {        
        try {
            helper.parseThrowException(new File(testpath + "typeResolutionInMethodFrame.key"));
        } catch (Throwable t) {
            return;
        }
        fail("Something with type resolution in method frames is corrupt. " +
                "The type Test should not be found in the default scope as it is " +
                "declared inside package test.");
    }
    
    public void testMethodFrameRedirectsScope() {        
        ProofAggregate pa = null;
        try {
            pa =
                helper.parseThrowException(new File(testpath + "typeResolutionInMethodFrame2.key"));
        } catch (Throwable t) {
            fail("Something with type resolution in method frames is corrupt. " +
                    "The type Test should be found as the scope to look for " +
                    "is redirected to test.Test");
        }                  
    }
}
