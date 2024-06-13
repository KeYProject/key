package de.uka.ilkd.key.util;


import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableArray;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Arrays;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;
import static de.uka.ilkd.key.logic.equality.ProofIrrelevancyProperty.PROOF_IRRELEVANCY_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingSourceElementProperty.RENAMING_SOURCE_ELEMENT_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static de.uka.ilkd.key.logic.equality.TermLabelsProperty.TERM_LABELS_PROPERTY;
import static org.junit.jupiter.api.Assertions.*;

public class TestLinkedHashMapWrapper {
    private TermBuilder tb;

    private TermFactory tf;

    final private TermLabel relevantLabel1 = ParameterlessTermLabel.UNDEFINED_VALUE_LABEL;
    final private TermLabel relevantLabel2 = ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL;
    private static TermLabel irrelevantLabel = null;
    final private static OriginTermLabelFactory factory = new OriginTermLabelFactory();

    @BeforeAll
    public static void setIrrelevantLabel() {
        try {
            irrelevantLabel = factory.parseInstance(Arrays.stream(new String[] {
                            "User_Interaction @ node 0 (Test Test)", "[]" }).toList(),
                    HelperClassForTests.createServices());
        } catch (TermLabelException e) {
            fail(e);
        }
    }

    @BeforeEach
    public void setUp() {
        tb = TacletForTests.services().getTermBuilder();
        tf = TacletForTests.services().getTermFactory();
    }

    @Test
    public void testRenamingProperty() {

    }

    @Test
    public void testTermLabelsProperty() {
        Term t1 = tb.tt();
    }

    @Test
    public void testIrrelevantTermLabelsProperty() {

    }

    @Test
    public void testProofIrrelevancyProperty() {

    }
}
