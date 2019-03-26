package de.uka.ilkd.key.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses(
        {
                de.uka.ilkd.key.logic.TestTermFactory.class,
                de.uka.ilkd.key.logic.TestTermLabelManager.class,
                de.uka.ilkd.key.logic.TestTermBuilder.class,
                de.uka.ilkd.key.logic.TestTerm.class,
                de.uka.ilkd.key.logic.TestNamespace.class,
                de.uka.ilkd.key.logic.TestSemisequent.class,
                de.uka.ilkd.key.logic.TestPosInOcc.class,
                de.uka.ilkd.key.logic.TestPosInTerm.class,
                de.uka.ilkd.key.logic.TestClashFreeSubst.class,
                de.uka.ilkd.key.logic.TestLocalSymbols.class,
                de.uka.ilkd.key.logic.TestSyntacticalReplaceVisitor.class,
                de.uka.ilkd.key.logic.TestVariableNamer.class,
                de.uka.ilkd.key.logic.LabeledTermImplTest.class})
public class LogicModelTests {
}