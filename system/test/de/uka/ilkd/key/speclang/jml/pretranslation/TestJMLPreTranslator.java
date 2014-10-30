// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


public class TestJMLPreTranslator extends TestCase {
    
    private ImmutableList<TextualJMLConstruct> parseMethodSpec(String ms) 
            throws SLTranslationException {
        KeYJMLPreParser preParser 
                = new KeYJMLPreParser(ms, "no file", Position.UNDEFINED);
        return preParser.parseClasslevelComment();
    }

    
    public void testSimpleSpec() throws SLTranslationException {
        ImmutableList<TextualJMLConstruct> constructs
            = parseMethodSpec(  "/*@ normal_behavior\n"
                              + "     requires true;\n"
                              + "  */");

        assertTrue(constructs != null);
        assertTrue(constructs.size() == 1);
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructs.head();
        
        assertTrue(specCase.getBehavior() == Behavior.NORMAL_BEHAVIOR);
        assertTrue(specCase.getRequires().size() == 1);
        assertTrue(specCase.getAssignable().size() == 0);
        assertTrue(specCase.getEnsures().size() == 0);
        assertTrue(specCase.getSignals().size() == 0);
        assertTrue(specCase.getSignalsOnly().size() == 0);
        
        assertTrue(specCase.getRequires().head().text.trim().equals("requires true;"));
    }
    

    public void testComplexSpec() throws SLTranslationException {
        ImmutableList<TextualJMLConstruct> constructs
            = parseMethodSpec(  "/*@ behaviour\n"
                              + "  @  requires true;\n"
                              + "  @  requires ((;;(;););(););\n" 
                              + "  @  ensures false;\n"
                              + "  @  signals exception;\n"
                              + "  @  signals_only onlythis;\n"
                              + "  @  assignable \\nothing;\n"
                              + "  @*/");

        assertTrue(constructs != null);
        assertTrue(constructs.size() == 1);
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructs.head();
                
        assertTrue(specCase.getBehavior() == Behavior.BEHAVIOR);
        assertTrue(specCase.getRequires().size() == 2);
        assertTrue(specCase.getAssignable().size() == 1);
        assertTrue(specCase.getEnsures().size() == 1);
        assertTrue(specCase.getSignals().size() == 1);
        assertTrue(specCase.getSignalsOnly().size() == 1);

        assertTrue(specCase.getEnsures().head().text.trim().equals("ensures false;"));
        assertTrue(specCase.getAssignable().head().text.trim().equals(
                "assignable \\nothing;"));
    }

    
    public void testMultipleSpecs() throws SLTranslationException {
        ImmutableList<TextualJMLConstruct> constructs 
            = parseMethodSpec(  "//@ normal_behaviour\n"
                              + "//@  ensures false\n"
                              + "//@          || true;\n"
                              + "//@  assignable \\nothing;\n"
                              + "//@ also exceptional_behaviour\n"
                              + "//@  requires o == null;\n"
                              + "//@  signals Exception;\n");
        
        assertTrue(constructs != null);
        assertTrue(constructs.size() == 2);
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        assertTrue(constructs.tail().head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase1 = (TextualJMLSpecCase) constructs.head();
        TextualJMLSpecCase specCase2 = (TextualJMLSpecCase) constructs.tail().head();

        assertTrue(specCase1.getBehavior() == Behavior.NORMAL_BEHAVIOR);
        assertTrue(specCase1.getRequires().size() == 0);
        assertTrue(specCase1.getAssignable().size() == 1);
        assertTrue(specCase1.getEnsures().size() == 1);
        assertTrue(specCase1.getSignals().size() == 0);
        assertTrue(specCase1.getSignalsOnly().size() == 0);
        
        assertTrue(specCase2.getBehavior() == Behavior.EXCEPTIONAL_BEHAVIOR);
        assertTrue(specCase2.getRequires().size() == 1);
        assertTrue(specCase2.getAssignable().size() == 0);
        assertTrue(specCase2.getEnsures().size() == 0);
        assertTrue(specCase2.getSignals().size() == 1);
        assertTrue(specCase2.getSignalsOnly().size() == 0);
    }

    
    public void testFailure() {
        try {
            parseMethodSpec("/*@ normal_behaviour \n @ signals ohoh;" + "  @*/");
            assertTrue(false);
        } catch (SLTranslationException e) {
            //fine
        }
    }
    
    
    public void testFailure2() {
        try {
            parseMethodSpec(  "/*@ behaviour\n"
                            + "  @  requires (;((;;);();();(();;;(;)));\n"
                            + "  @*/");
            assertTrue(false);
        } catch (SLTranslationException e) {
            //fine
        }
    }
}