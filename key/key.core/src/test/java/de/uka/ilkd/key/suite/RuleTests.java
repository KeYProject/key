package de.uka.ilkd.key.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
        de.uka.ilkd.key.rule.TestSchemaModalOperators.class,
        de.uka.ilkd.key.rule.tacletbuilder.TestTacletBuild.class,
        de.uka.ilkd.key.rule.TestCollisionResolving.class,
        de.uka.ilkd.key.rule.TestMatchTaclet.class,
        de.uka.ilkd.key.rule.match.legacy.TestLegacyTacletMatch.class,
        de.uka.ilkd.key.rule.match.vm.VMTacletMatcherTest.class,
        de.uka.ilkd.key.rule.TestApplyTaclet.class,
        de.uka.ilkd.key.rule.inst.TestGenericSortInstantiations.class,
        de.uka.ilkd.key.rule.metaconstruct.TestProgramMetaConstructs.class,
        de.uka.ilkd.key.rule.conditions.TestDropEffectlessElementary.class,
        de.uka.ilkd.key.rule.merge.MergeRuleTests.class
})
public class RuleTests {
}
