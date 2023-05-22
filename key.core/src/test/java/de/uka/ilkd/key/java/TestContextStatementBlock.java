package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.util.ExtList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class TestContextStatementBlock {

    JavaBlock blockOne;

    @BeforeEach
    public void setUp() {
        Services services = TacletForTests.services();
        JavaService c2k = new JavaService(services, Collections.emptyList());
        blockOne = c2k.readBlock("{int a=1; {int b=3; b++;} a++;}", c2k.createEmptyContext(), null);
    }

    @AfterEach
    public void tearDown() {
        blockOne = null;
    }

    @Test
    public void testContextTermInstantiation() {
        ExtList statementList = new ExtList();
        StatementBlock stContainer = (StatementBlock) blockOne.program();
        int size = stContainer.getChildCount();
        assertEquals(3, size, "Wrong size. Should have only 3 children");
        PosInProgram prefixEnd = PosInProgram.TOP.down(0);
        assertTrue(
            PosInProgram.getProgramAt(prefixEnd,
                blockOne.program()) instanceof LocalVariableDeclaration,
            "Prefix should end with an assignment");
        PosInProgram suffixStart = PosInProgram.TOP.down(2);
        assertTrue(
            PosInProgram.getProgramAt(suffixStart, blockOne.program()) instanceof PostIncrement,
            "Suffix should start with an ++");
        for (int i = size - 2; i >= 1; i--) {
            statementList.add(stContainer.getChildAt(i));
        }

    }


}
